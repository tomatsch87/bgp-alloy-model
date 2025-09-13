module main

open autonomous_system
open bgp_connection
open bgp_message
open message_queue
open routing_table

pred stutter {
    stutterAS
    stutterBGPConnection
    stutterBGPMessage
    stutterMessageQueue
    stutterRoutingTable
}

pred init {
    initAS
    initBGPConnection
    initBGPMessage
    initMessageQueue
    initRoutingTable
}

fact {
    init
    // No empty models
    #AS > 1

    // Allowed events
    // Only allow activateAll, connectAll, establishAll, initiateAll to save timesteps and enforce more meaningful models
    always (
        stutter or
        // (some a: AS | activate[a]) or
        activateAll or
        // (some a, b: AS | connectAtoB[a, b]) or
        connectAll or
        // (some a, b: AS | establish[a, b]) or
        establishAll or
        // (some a, b: AS | initiate[a, b]) or
        (some a: AS | initiateAll[a]) or
        (some a: AS | processMessage[a])
    )
}

// -- RUN PREDICATES FOR VISUALIZATION --
// Run to visualize BGP establishing connections
// Load theme: establish.thm
run establishConnections {
    #AS = 3
    #neighbors = 6

    // Eventually there is a Connection in Established state
    eventually some c: BGPConnection | c.connectionState = Established
} for 6 but 4 steps

// Run to visualize an AS initiating with its neighbors
// Load theme: initiate.thm
run initiateAS {
    #AS = 3
    #neighbors = 6

    // Eventually some AS initiates a message to all neighbors
    // eventually some a: AS | initiateAll[a]

    // Eventually three Message Queues have messages (requires 2 initiations)
    eventually some disj a, b, c: AS | #a.messageQueue.messages > 0 and #b.messageQueue.messages > 0 and #c.messageQueue.messages > 0
} for 6 but 6 steps

// Run to visualize a route propagation
// Load theme: propagate.thm
run propagateRoutes {
    #AS = 3
    #neighbors = 6

    // Eventually some AS process a message and propagates a route to all neighbors
    eventually some a: AS | processMessage[a]
} for 6 but 6 steps

// Run to visualize a basic BGP example with all Atoms including 3 ASes that are fully connected
// Load theme: main.thm or main_reduced.thm
run main {
    #AS = 3
    #neighbors = 6

    // Eventually there are two ASes with a routing table with >= 3 entries
    // Set Atoms=6 and Steps=9
    // eventually some disj a, b: AS | #a.routingTable.entries >= 3 and #b.routingTable.entries >= 3

    // Eventually there are three ASes with a routing table with >= 3 entries
    // Set Atoms=9 and Steps=13 also set maximum Memory in Alloy Analyzer to 8GB or more
    // THIS MAY TAKE A LONG TIME TO RUN!
    eventually some disj a, b, c: AS | #a.routingTable.entries >= 3 and #b.routingTable.entries >= 3 and #c.routingTable.entries >= 3
} for 9 but 13 steps

// -- ASSERTS FOR CHECKING THE BGP SPECIFICATION --
// Reference: bgp_rfc4271.pdf

// 1. SAFETY: We only forward the most preferred route (shortest ASPath in our case)
// "In the context of this document, we assume that a BGP speaker
// advertises to its peers only those routes that it uses itself (in
// this context, a BGP speaker is said to 'use' a BGP route if it is the
// most preferred BGP route and is used in forwarding)." - Page 5, RFC 4271
assert onlyMostPreferredRoute {
    all msg: BGPMessage | shortestKnownRoute[msg.advertisedRoute, msg.from.routingTable.entries]
}

check onlyMostPreferredRoute for 6 but 10 steps

// 2. SAFETY: We only forward valid routes (no loops, no invalid nextHops)
// "If the NEXT_HOP attribute of a BGP route depicts an address that is
// not resolvable, or if it would become unresolvable if the route was
// installed in the routing table, the BGP route MUST be excluded from
// the Phase 2 decision function."
// "If the AS_PATH attribute of a BGP route contains an AS loop, the BGP
// route should be excluded from the Phase 2 decision function." - Page 78, RFC 4271
assert noInvalidRoutes {
    all msg: BGPMessage | not checkLoop[msg.advertisedRoute] and
        some msg.advertisedRoute.nextHop and
        one c: BGPConnection | c.from = msg.to and c.to = msg.advertisedRoute.nextHop and c.connectionState = Established
}

check noInvalidRoutes for 6 but 10 steps

// WEAK FAIRNESS: Every event that is eventually always possible, will always eventually happen
pred weakFairness {
    all a: AS | {
        (eventually always a.state = Idle)
            implies (always eventually activateAll)
        (eventually always some b: AS | a != b and a.state = Active and b.state = Active and
            b in a.neighbors and no c: BGPConnection | c.from = a and c.to = b)
            implies (always eventually connectAll)
        (eventually always some b: AS | a != b and
            one c1: BGPConnection | c1.from = a and c1.to = b and c1.connectionState = Connect and
            one c2: BGPConnection | c2.from = b and c2.to = a and c2.connectionState = Connect)
            implies (always eventually establishAll)
        (eventually always some b: AS | b != a and
            a.state = Active and b.state = Active and
            one ca: BGPConnection | ca.from = a and ca.to = b and ca.connectionState = Established and
            one cb: BGPConnection | cb.from = b and cb.to = a and cb.connectionState = Established)
            implies (always eventually initiateAll[a])
        (eventually always a.state = Active and
            some msg: BGPMessage | msg in elems[a.messageQueue.messages])
            implies (always eventually processMessage[a])
    }
}

// LIVENESS: Eventually some route propagation will happen
// Assume weakFairness holds (no inifinite stuttering)
assert AtLeastOneRoutePropagation { weakFairness implies eventually (some rt: RoutingTable | #rt.entries > 1) }
// You may need to set the maximum Memory in Alloy Analyzer to 8GB or more
// THIS MAY TAKE A LONG TIME TO RUN!
check AtLeastOneRoutePropagation for 9 but 20 steps
// Alternatively run this:
check AtLeastOneRoutePropagation for 3 AS, 3 ASN, 3 Prefix, 6 BGPConnection, 3 MessageQueue, 3 RoutingTable, 8 Message, 9 RoutingEntry
