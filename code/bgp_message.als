module bgp_message

open signatures
open message_queue

pred initBGPMessage {
    no BGPMessage
}

pred stutterBGPMessage {
    BGPMessage' = BGPMessage
    all msg: BGPMessage | msg.from' = msg.from and msg.to' = msg.to and msg.type' = msg.type and msg.advertisedRoute' = msg.advertisedRoute
}

// ForwardRoute creates a new routing entry for AS b based on the routing entry from AS a
// For this, it sets the next hop to a and prepends a's ASN to the AS path
// Then it constructs a new BGPMessage to send this routing entry to AS b and pushes it to b's message queue
pred forwardRoute[a, b: AS, route: RoutingEntry] {
    // Create new RoutingEntry for B using A's routing entry
    some re: RoutingEntry' - RoutingEntry | {
        // Set the next hop to A and prepend A's ASN to the AS path
        re.prefix'       = route.prefix
        re.nextHop'      = a
        re.ASPath'      = route.ASPath.insert[0, a.asn]

        // Construct the new update message
        some msg: BGPMessage' - BGPMessage | {
            // Set the message fields from A to B, type Update, and the new routing entry
            msg.from'       = a
            msg.to'         = b
            msg.type'       = Update
            msg.advertisedRoute' = re

            // The message is added to the message queue of b
            pushMessage[b.messageQueue, msg]
        }
    }
}

// BroadcastRoute creates new routing entries for all ASes in set b based on the routing entry from AS a
// For each AS in b, it sets the next hop to a and prepends a's ASN to the AS path
// Then it constructs new BGPMessages to send this routing entry to all ASes in b and pushes them to their message queues
pred broadcastRoute[a: AS, b: set AS, route: RoutingEntry] {
    // Create new RoutingEntries for each AS in b using A's routing entry
    all dest: b | some re: RoutingEntry' - RoutingEntry | {
        // Set the next hop to A and prepend A's ASN to the AS path
        re.prefix'       = route.prefix
        re.nextHop'      = a
        re.ASPath'      = route.ASPath.insert[0, a.asn]

        // Construct the new update message for this destination
        some msg: BGPMessage' - BGPMessage | {
            // Set the message fields from A to dest, type Update, and the new routing entry
            msg.from'       = a
            msg.to'         = dest
            msg.type'       = Update
            msg.advertisedRoute' = re

            // The message is added to the message queue of dest
            pushMessage[dest.messageQueue, msg]
        }
    }
}
