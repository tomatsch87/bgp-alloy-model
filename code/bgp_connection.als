module bgp_connection

open signatures

pred initBGPConnection {
    no BGPConnection
}

pred stutterBGPConnection {
    BGPConnection' = BGPConnection
    all c: BGPConnection | c.connectionState' = c.connectionState and c.from' = c.from and c.to' = c.to
}

// Connect creates a new connection from one AS a to another AS b
// Checks that both AS are in Active state and that they are neighbors
// The connection is created in Connect state
pred connectAtoB[a, b: AS] {
    // precondition
    a.state = Active
    b.state = Active
    a != b
    a in b.neighbors
    b in a.neighbors
    // Ensure no existing connection from a to b
    no c: BGPConnection | c.from = a and c.to = b
    // postcondition
    // Exactly one new connection is created from a to b in Connect state
    #(BGPConnection' - BGPConnection) = 1
    all c: BGPConnection' - BGPConnection | c.from' = a and c.to' = b and c.connectionState' = Connect

    // frame condition
    state' = state
    // Existing connections remain unchanged
    all c: BGPConnection | c in BGPConnection' and c.connectionState' = c.connectionState and c.from' = c.from and c.to' = c.to
    BGPMessage' = BGPMessage
    all mq: MessageQueue | mq.messages' = mq.messages
    all msg: BGPMessage | msg.from' = msg.from and msg.to' = msg.to and msg.type' = msg.type and msg.advertisedRoute' = msg.advertisedRoute
    RoutingEntry' = RoutingEntry
    all rt: RoutingTable | rt.entries' = rt.entries
    all re: RoutingEntry | re.prefix' = re.prefix and re.nextHop' = re.nextHop and re.ASPath' = re.ASPath
}


// ConnectAll creates symmetric connections between all AS neighbor pairs
// Enforces that all valid active AS neighbor pairs are connected in both directions
pred connectAll {
    // precondition
    // At least one valid AS pair exists that can be connected
    some disj a, b: AS | a.state = Active and b.state = Active and b in a.neighbors and
        no c: BGPConnection | c.from = a and c.to = b
    
    // postcondition
    // Use let binding to define valid pairs
    let validPairs = {disj a, b: AS | a.state = Active and b.state = Active and b in a.neighbors and
        no c: BGPConnection | c.from = a and c.to = b} |
    {
        // Create connections for all valid pairs
        all a, b: AS | a->b in validPairs implies
            one c: BGPConnection' - BGPConnection | c.from' = a and c.to' = b and c.connectionState' = Connect
        
        // Only create connections for valid pairs
        all c: BGPConnection' - BGPConnection | 
            some a, b: AS | a->b in validPairs and c.from' = a and c.to' = b
    }
    // Ensure no duplicate connections
    all c1, c2: BGPConnection' - BGPConnection | c1.from' = c2.from' and c1.to' = c2.to' implies c1 = c2

    // frame condition
    state' = state
    // Existing connections remain unchanged
    all c: BGPConnection | c in BGPConnection' and c.connectionState' = c.connectionState and c.from' = c.from and c.to' = c.to
    BGPMessage' = BGPMessage
    all mq: MessageQueue | mq.messages' = mq.messages
    all msg: BGPMessage | msg.from' = msg.from and msg.to' = msg.to and msg.type' = msg.type and msg.advertisedRoute' = msg.advertisedRoute
    RoutingEntry' = RoutingEntry
    all rt: RoutingTable | rt.entries' = rt.entries
    all re: RoutingEntry | re.prefix' = re.prefix and re.nextHop' = re.nextHop and re.ASPath' = re.ASPath
}

// Establish moves a connection from Connect state to Established state
// Checks that both AS have a connection from a to b and from b to a in Connect state
// The connection is moved to Established state
pred establish[a, b: AS] {
    // precondition
    one ca: BGPConnection | ca.from = a and ca.to = b and ca.connectionState = Connect
    one cb: BGPConnection | cb.from = b and cb.to = a and cb.connectionState = Connect

    // postcondition
    one ca: BGPConnection' | ca.from' = a and ca.to' = b and ca.connectionState' = Established
    one cb: BGPConnection' | cb.from' = b and cb.to' = a and cb.connectionState' = Established

    // frame condition
    state' = state
    BGPConnection' = BGPConnection
    all c: BGPConnection' | c.from' = c.from and c.to' = c.to
    // Only the specific symmetric connections between a and b change state to Established
    all c: BGPConnection' | (c.from' != a or c.to' != b) and (c.from' != b or c.to' != a) implies c.connectionState' = c.connectionState
    BGPMessage' = BGPMessage
    all mq: MessageQueue | mq.messages' = mq.messages
    all msg: BGPMessage | msg.from' = msg.from and msg.to' = msg.to and msg.type' = msg.type and msg.advertisedRoute' = msg.advertisedRoute
    RoutingEntry' = RoutingEntry
    all rt: RoutingTable | rt.entries' = rt.entries
    all re: RoutingEntry | re.prefix' = re.prefix and re.nextHop' = re.nextHop and re.ASPath' = re.ASPath
}


// EstablishAll moves connections from Connect state to Established state
// Automatically establishes all symmetric connection pairs that are in Connect state
pred establishAll {
    // precondition
    // At least one symmetric Connect pair exists
    some disj a, b: AS |
        one c1: BGPConnection | c1.from = a and c1.to = b and c1.connectionState = Connect and
        one c2: BGPConnection | c2.from = b and c2.to = a and c2.connectionState = Connect
    
    // postcondition
    // Use a let binding to define valid pairs
    let validPairs = {disj a, b: AS |
        one c1: BGPConnection | c1.from = a and c1.to = b and c1.connectionState = Connect and
        one c2: BGPConnection | c2.from = b and c2.to = a and c2.connectionState = Connect} |
    {
        // Establish all valid pairs
        all a, b: AS | a->b in validPairs implies {
            one c1: BGPConnection' | c1.from' = a and c1.to' = b and c1.connectionState' = Established
            one c2: BGPConnection' | c2.from' = b and c2.to' = a and c2.connectionState' = Established
        }
        
        // Only connections in valid pairs change state
        all c: BGPConnection' | 
            (no a, b: AS | a->b in validPairs and 
                ((c.from' = a and c.to' = b) or (c.from' = b and c.to' = a)))
            implies c.connectionState' = c.connectionState
    }

    // frame condition
    state' = state
    BGPConnection' = BGPConnection
    all c: BGPConnection' | c.from' = c.from and c.to' = c.to
    BGPMessage' = BGPMessage
    all mq: MessageQueue | mq.messages' = mq.messages
    all msg: BGPMessage | msg.from' = msg.from and msg.to' = msg.to and msg.type' = msg.type and msg.advertisedRoute' = msg.advertisedRoute
    RoutingEntry' = RoutingEntry
    all rt: RoutingTable | rt.entries' = rt.entries
    all re: RoutingEntry | re.prefix' = re.prefix and re.nextHop' = re.nextHop and re.ASPath' = re.ASPath
}