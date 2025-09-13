module autonomous_system

open signatures
open bgp_message

pred initAS {
    // All Autonomous Systems start in Idle state
    all a: AS | a.state = Idle
    // No AS is their own neighbor
    all a: AS | a not in a.neighbors
    // The neighbor relation is symmetric
    all a: AS | a.neighbors = neighbors.a
    // The model is fully connected
    all a: AS | AS = a.*neighbors
    // All ASes have a unique message queue
    all a, b: AS | a != b implies a.messageQueue != b.messageQueue
    // All ASes have a unique routing table
    all a, b: AS | a != b implies a.routingTable != b.routingTable
    // All ASes have a unique ASN and Prefix
    all a, b: AS | a != b implies a.asn != b.asn and a.prefix != b.prefix
    // There are no other ASNs and Prefixes than those assigned to ASes
    ASN = AS.asn
    Prefix = AS.prefix
}

pred stutterAS {
    state' = state
}

// Activate brings an AS from Idle to Active state
pred activate[a: AS] {
    // precondition
    a.state = Idle

    // postcondition
    a.state' = Active

    // frame condition
    all b: AS - a | b.state' = b.state
    BGPConnection' = BGPConnection
    all c: BGPConnection | c.connectionState' = c.connectionState and c.from' = c.from and c.to' = c.to
    BGPMessage' = BGPMessage
    all mq: MessageQueue | mq.messages' = mq.messages
    all msg: BGPMessage | msg.from' = msg.from and msg.to' = msg.to and msg.type' = msg.type and msg.advertisedRoute' = msg.advertisedRoute
    RoutingEntry' = RoutingEntry
    all rt: RoutingTable | rt.entries' = rt.entries
    all re: RoutingEntry | re.prefix' = re.prefix and re.nextHop' = re.nextHop and re.ASPath' = re.ASPath
}

// ActivateAll brings all ASes from Idle to Active state
pred activateAll {
    // precondition
    some a: AS | a.state = Idle

    // postcondition
    all a: AS | a.state' = Active

    // frame condition
    BGPConnection' = BGPConnection
    all c: BGPConnection | c.connectionState' = c.connectionState and c.from' = c.from and c.to' = c.to
    BGPMessage' = BGPMessage
    all mq: MessageQueue | mq.messages' = mq.messages
    all msg: BGPMessage | msg.from' = msg.from and msg.to' = msg.to and msg.type' = msg.type and msg.advertisedRoute' = msg.advertisedRoute
    RoutingEntry' = RoutingEntry
    all rt: RoutingTable | rt.entries' = rt.entries
    all re: RoutingEntry | re.prefix' = re.prefix and re.nextHop' = re.nextHop and re.ASPath' = re.ASPath
}

// Initiate starts the BGP process of exchanging routing information
// All ASes start with their internal prefix in their routing table represented by a RoutingEntry
// Initiate for A sends the internal prefix to B
pred initiate[a, b: AS] {
    // precondition
    a.state = Active and b.state = Active
    // A and B have an established connection
    one ca: BGPConnection | ca.from = a and ca.to = b and ca.connectionState = Established
    one cb: BGPConnection | cb.from = b and cb.to = a and cb.connectionState = Established
    // A is only allowed to initiate to B if B has never received a message from A for A's prefix
    historically no msg: BGPMessage | msg in elems[b.messageQueue.messages] and 
        msg.advertisedRoute.prefix = a.prefix and msg.from = a

    // Use a let binding to define the internal prefix (the entry which has no next hop)
    let internalPrefix = {re: RoutingEntry | re in a.routingTable.entries and no re.nextHop} | {
        one internalPrefix

        // postcondition
        // A sends its internal prefix to B using forwardRoute
        forwardRoute[a, b, internalPrefix]
    }
    // Ensure only one new RoutingEntry is created
    #(RoutingEntry' - RoutingEntry) = 1
    // Ensure only one new BGPMessage is created
    #(BGPMessage' - BGPMessage) = 1

    // frame condition
    state' = state
    BGPConnection' = BGPConnection
    all c: BGPConnection | c.connectionState' = c.connectionState and c.from' = c.from and c.to' = c.to
    all mq: MessageQueue - b.messageQueue | mq.messages' = mq.messages
    all omsg: BGPMessage | omsg.from' = omsg.from and omsg.to' = omsg.to and omsg.type' = omsg.type and omsg.advertisedRoute' = omsg.advertisedRoute
    all rt: RoutingTable | rt.entries' = rt.entries
    all ore: RoutingEntry | ore.prefix' = ore.prefix and ore.nextHop' = ore.nextHop and ore.ASPath' = ore.ASPath
}

// InitiateAll enforces AS a to initiate with all of its established connections
// A broadcasts its internal prefix to all ASes it has established connections with
pred initiateAll[a: AS] {
    // precondition
    a.state = Active
    // A has a established connection
    some b: AS | b != a and b.state = Active and
        one ca: BGPConnection | ca.from = a and ca.to = b and ca.connectionState = Established and
        one cb: BGPConnection | cb.from = b and cb.to = a and cb.connectionState = Established

    // Use a let binding to define the established neighbors
    let establishedNeighbors = {b: AS | b != a and b.state = Active and
        one ca: BGPConnection | ca.from = a and ca.to = b and ca.connectionState = Established and
        one cb: BGPConnection | cb.from = b and cb.to = a and cb.connectionState = Established} |
    {
        // If at least one established neighbor exists A initiates
        // Else it does not initiate
        some establishedNeighbors
            implies {
                // A is only allowed to initiateAll if it has never sent messages with its prefix directly to its neighbors
                historically all dest: establishedNeighbors | no msg: BGPMessage | {
                    msg in elems[dest.messageQueue.messages] and msg.advertisedRoute.prefix = a.prefix and msg.from = a
                }

                // Use a let binding to define the internal prefix (the entry which has no next hop)
                let internalPrefix = {re: RoutingEntry | re in a.routingTable.entries and no re.nextHop} | {
                    one internalPrefix

                    // postcondition
                    // A broadcasts its internal prefix to all established neighbors
                    broadcastRoute[a, establishedNeighbors, internalPrefix]
                }
                // Ensure only one new RoutingEntry is created
                #(RoutingEntry' - RoutingEntry) = 1
                // Ensure only one new BGPMessage is created for each established neighbor
                #(BGPMessage' - BGPMessage) = #establishedNeighbors

                // frame condition
                all mq: MessageQueue - establishedNeighbors.messageQueue | mq.messages' = mq.messages
            } else {
                // frame condition
                BGPMessage' = BGPMessage
                all mq: MessageQueue | mq.messages' = mq.messages
                RoutingEntry' = RoutingEntry
            }
    }
    
    // frame condition
    state' = state
    BGPConnection' = BGPConnection
    all c: BGPConnection | c.connectionState' = c.connectionState and c.from' = c.from and c.to' = c.to
    all omsg: BGPMessage | omsg.from' = omsg.from and omsg.to' = omsg.to and omsg.type' = omsg.type and omsg.advertisedRoute' = omsg.advertisedRoute
    all rt: RoutingTable | rt.entries' = rt.entries
    all ore: RoutingEntry | ore.prefix' = ore.prefix and ore.nextHop' = ore.nextHop and ore.ASPath' = ore.ASPath
}

// ProcessMessage processes a message from the message queue of an AS
// It dequeues the first message from the message queue and checks if it is a valid advertised route
// If it is valid, it adds the route to the routing table 
// And if it is the shortest known route, it broadcasts it to all established neighbors (excluding the sender)
pred processMessage[a: AS] {
    // precondition
    a.state = Active
    // A has a message in its queue
    some msg: BGPMessage | msg in elems[a.messageQueue.messages]

    // Use a let binding to define the first message in the queue
    let message = {msg: BGPMessage | msg in first[a.messageQueue.messages]} | {
        // postcondition
        // Dequeue the first message from the message queue
        a.messageQueue.messages' = delete[a.messageQueue.messages, 0]

        // If the route is not already in the routing table we process it
        // Else we do not process the message
        not message.advertisedRoute in a.routingTable.entries
            implies {
                // Process the message
                // If there is a loop in the AS path with a's ASN, it is not processed (not a valid route)
                // Else we add the route to a's routing table and broadcast it to all established neighbors (except the sender)
                checkLoopWithASN[message.advertisedRoute, a.asn]
                    implies {
                        // There is a loop, so we do not process the message
                        // frame condition
                        BGPMessage' = BGPMessage
                        all mq: MessageQueue - a.messageQueue | mq.messages' = mq.messages
                        RoutingEntry' = RoutingEntry
                        a.routingTable.entries' = a.routingTable.entries
                    } else {
                        // No loop, so we process the message
                        // Add the advertised route to a's routing table
                        a.routingTable.entries' = a.routingTable.entries + message.advertisedRoute

                        // If the advertised route is the shortest known route, we broadcast it to all established neighbors
                        // excluding the sender of the message
                        // Else we do not broadcast the route
                        shortestKnownRoute[message.advertisedRoute, a.routingTable.entries]
                            implies {
                                // Use a let binding to define the destinations excluding the sender
                                let destinations = {b: AS | b != a and b.state = Active and 
                                    b != message.from and
                                    one ca: BGPConnection | ca.from = a and ca.to = b and ca.connectionState = Established and
                                    one cb: BGPConnection | cb.from = b and cb.to = a and cb.connectionState = Established} |
                                {
                                    // If there are any destinations broadcast the route
                                    // Else we do nothing
                                    some destinations
                                        implies {
                                            // Broadcast the route to all destinations
                                            broadcastRoute[a, destinations, message.advertisedRoute]

                                            // Ensure only one new RoutingEntry
                                            #(RoutingEntry' - RoutingEntry) = 1
                                            // Ensure only one new BGPMessage for each destination
                                            #(BGPMessage' - BGPMessage) = #destinations

                                            // frame condition
                                            all mq: MessageQueue - a.messageQueue - destinations.messageQueue | mq.messages' = mq.messages
                                        } else {
                                            // frame condition
                                            BGPMessage' = BGPMessage
                                            all mq: MessageQueue - a.messageQueue | mq.messages' = mq.messages
                                            RoutingEntry' = RoutingEntry
                                        }
                                }
                            } else {
                                // frame condition
                                BGPMessage' = BGPMessage
                                all mq: MessageQueue - a.messageQueue | mq.messages' = mq.messages
                                RoutingEntry' = RoutingEntry
                            }
                    }
            } else {
                // frame condition
                BGPMessage' = BGPMessage
                all mq: MessageQueue - a.messageQueue | mq.messages' = mq.messages
                RoutingEntry' = RoutingEntry
                a.routingTable.entries' = a.routingTable.entries
            }
    }
    // frame condition
    state' = state
    BGPConnection' = BGPConnection
    all c: BGPConnection | c.connectionState' = c.connectionState and c.from' = c.from and c.to' = c.to
    all msg: BGPMessage | msg.from' = msg.from and msg.to' = msg.to and msg.type' = msg.type and msg.advertisedRoute' = msg.advertisedRoute
    all rt: RoutingTable - a.routingTable | rt.entries' = rt.entries
    all re: RoutingEntry | re.prefix' = re.prefix and re.nextHop' = re.nextHop and re.ASPath' = re.ASPath
}

// CheckLoopWithASN checks if the AS path of a routing entry contains the ASN
// If it does, the routing entry is not processed
// This is used to prevent routing loops in the BGP process
pred checkLoopWithASN[route: RoutingEntry, asn: ASN] {
    asn in elems[route.ASPath]
}

// CheckLoop checks if the AS path of a routing entry contains a loop
// A loop is defined as the same ASN appearing more than once in the AS path
// If it does, the routing entry is invalid
// This is used to verify the route propagation process
pred checkLoop[route: RoutingEntry] {
    // Use a let binding to define the AS path elements
    let pathElems = elems[route.ASPath] | {
        // If the AS path is empty, there is no loop
        not no pathElems or {
            // If the AS path has more than one element, check for loops
            #pathElems > 1 implies {
                // Check if the AS path contains a loop
                not all e1, e2: pathElems | e1 != e2
            }
        }
    }
}

// ShortestKnownRoute checks if the advertised route is the shortest known route for the given prefix
// It compares the advertised route with the existing routes in the routing table
// It uses the ASPath length to compare the routes
pred shortestKnownRoute[route: RoutingEntry, entries: set RoutingEntry] {
    // Use a let binding to define the existing routes with the same prefix
    let existingRoutes = {re: RoutingEntry | re in entries and re.prefix = route.prefix} | {
        // If there are no existing routes with the same prefix, the route is the shortest known route
        no existingRoutes or {
            // Compare the route's ASPath length with all existing routes with the same prefix
            // Holds if the length is shorter or equal to the shortest existing route
            all er: existingRoutes | #(elems[route.ASPath]) <= #(elems[er.ASPath])
        }
    }
}
