module signatures

// --- Abstract ---
abstract sig State {}
abstract var sig Message {}
abstract sig MessageType {}

// --- Autonomous System ---
sig ASN {}
sig Prefix {}
sig AS {
    asn: one ASN,
    prefix: one Prefix,
    neighbors: set AS,
    var state: one ASState,
    messageQueue: one MessageQueue,
    routingTable: one RoutingTable
}
abstract sig ASState extends State {}
one sig Idle extends ASState {}
one sig Active extends ASState {}

// --- BGP Connection ---
var sig BGPConnection {
    var from: one AS,
    var to: one AS,
    var connectionState: one ConnectionState
}
abstract sig ConnectionState extends State {}
one sig Established extends ConnectionState {}
one sig Connect extends ConnectionState {}

// --- Message Queue ---
sig MessageQueue {
    var messages: seq BGPMessage
}

// --- BGP Message ---
var sig BGPMessage extends Message {
    var from: one AS,
    var to: one AS,
    var type: one MessageType,
    var advertisedRoute: one RoutingEntry
}
one sig Update extends MessageType {}

// --- Routing Table ---
sig RoutingTable {
    var entries: set RoutingEntry
}
var sig RoutingEntry {
    var prefix: one Prefix,
    var nextHop: lone AS,
    var ASPath: seq ASN
}
