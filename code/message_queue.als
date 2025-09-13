module message_queue

open signatures

pred initMessageQueue {
    // Initialize the message queues with no messages
    all mq: MessageQueue | no mq.messages
    // All MessageQueues belong to an AS
    all mq: MessageQueue | mq in AS.messageQueue
}

pred stutterMessageQueue {
    all mq: MessageQueue | mq.messages' = mq.messages
}

pred pushMessage[mq: MessageQueue, msg: BGPMessage] {
    // precondition
    // Only allow pushing new messages
    not msg in elems[mq.messages]
    // postcondition
    mq.messages' = mq.messages.add[msg]
    // frame condition
    // Existing message queues remain unchanged
    // all mqs: MessageQueue - mq | mqs.messages' = mqs.messages
}

pred popMessage[mq: MessageQueue] {
    // precondition
    #elems[mq.messages] > 0
    // postcondition
    mq.messages' = mq.messages.delete[0]
    // frame condition
    // Existing message queues remain unchanged
    // all mqs: MessageQueue - mq | mqs.messages' = mqs.messages
}

run {
    initMessageQueue

    always (
        stutterMessageQueue or
        (some mq: MessageQueue, msg: BGPMessage | pushMessage[mq, msg]) or
        (some mq: MessageQueue | popMessage[mq])
    )

    #MessageQueue > 1
    #BGPMessage > 1
    // Eventually, a message is pushed to a message queue
    eventually some mq: MessageQueue, msg: BGPMessage | pushMessage[mq, msg]
    // Eventually, a message queue has messages
    eventually some mq: MessageQueue | #mq.messages > 3
    // Eventually, a message is popped from a message queue
    eventually some mq: MessageQueue | popMessage[mq]
} for 6 but 10 steps
