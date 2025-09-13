module routing_table

open signatures

pred initRoutingTable {
    // All RoutingTables belong to an AS
    all rt: RoutingTable | rt in AS.routingTable
    // All ASes start with their own prefix with no next hop and an empty AS path in their routing table
    // This means they can reach themselves directly
    all a: AS | {
        #a.routingTable.entries = 1
        one re: RoutingEntry | {
            re.prefix = a.prefix
            no re.nextHop
            #elems[re.ASPath] = 0
            re in a.routingTable.entries
        }
    }
    // There are no other routing entries initially
    all re: RoutingEntry | some a: AS | re in a.routingTable.entries
}

pred stutterRoutingTable {
    all rt: RoutingTable | rt.entries' = rt.entries
    RoutingEntry' = RoutingEntry
    all re: RoutingEntry | re.prefix' = re.prefix and re.nextHop' = re.nextHop and re.ASPath' = re.ASPath
}

pred addEntry[rt: RoutingTable, re: RoutingEntry] {
    // precondition
    // Only allow adding new entries
    not re in rt.entries
    // postcondition
    rt.entries' = rt.entries + re
    // frame condition
    // Existing routing tables remain unchanged
    // all rts: RoutingTable - rt | rts.entries' = rts.entries
}

pred removeEntry[rt: RoutingTable, re: RoutingEntry] {
    // precondition
    #rt.entries > 0
    // postcondition
    rt.entries' = rt.entries - re
    // frame condition
    // Existing routing tables remain unchanged
    // all rts: RoutingTable - rt | rts.entries' = rts.entries
}

run {
    initRoutingTable

    always (
        stutterRoutingTable or
        (some rt: RoutingTable, re: RoutingEntry | addEntry[rt, re]) or
        (some rt: RoutingTable, re: RoutingEntry | removeEntry[rt, re])
    )

    #RoutingTable > 1
    #RoutingEntry > 1
    // Eventually, an entry is added to a routing table
    eventually some rt: RoutingTable, re: RoutingEntry | addEntry[rt, re]
    // Eventually, a routing table has entries
    eventually some rt: RoutingTable | #rt.entries > 3
    // Eventually, an entry is removed from a routing table
    eventually some rt: RoutingTable, re: RoutingEntry | removeEntry[rt, re]
} for 6 but 10 steps