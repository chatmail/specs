from pgmc import (
    immediate_create_group,
    AddMemberMessage,
    DelMemberMessage,
    ChatMessage,
    Relay,
)


def test_add_and_remove():
    relay = Relay(numpeers=4)
    p0, p1, p2, p3 = relay.get_peers()

    # create group
    immediate_create_group([p0, p1])
    assert p0.members == p1.members == set([p0.id, p1.id])
    assert p0.current_clock == p1.current_clock

    # add members
    with relay.queue_all_and_deliver():
        AddMemberMessage(p0, member=p2.id)
        AddMemberMessage(p0, member=p3.id)

    relay.assert_group_consistency()

    with relay.queue_all_and_deliver():
        DelMemberMessage(p3, member=p0.id)

    relay.assert_group_consistency()


def test_concurrent_add():
    relay = Relay(numpeers=4)
    p0, p1, p2, p3 = relay.get_peers()

    immediate_create_group([p0, p1])
    with relay.queue_all_and_deliver():
        # concurrent addition of two group members
        AddMemberMessage(p1, member=p2.id)
        AddMemberMessage(p0, member=p3.id)

    # p0 and p1 know now of each others additions
    # so need to send a message to get overall consistent membership
    with relay.queue_all_and_deliver():
        ChatMessage(p0)

    relay.assert_group_consistency()


def test_add_remove_and_stale_member_sends_chatmessage():
    relay = Relay(numpeers=4)
    p0, p1, p2, p3 = relay.get_peers()

    immediate_create_group([p0, p1, p2, p3])

    # p0 deleted p2 while p3 is offline
    with relay.queue_all_and_deliver(offline=[p3]):
        DelMemberMessage(p0, member=p2.id)

    # offline p3 sends a message with old memberlist and goes online
    with relay.queue_all_and_deliver():
        ChatMessage(p3)

    relay.assert_group_consistency()

    with relay.queue_all_and_deliver():
        ChatMessage(p0)

    assert p0.members == set(["p0", "p1", "p3"])


def test_add_remove_and_stale_member_sends_addition():
    relay = Relay(numpeers=5)
    p0, p1, p2, p3, p4 = relay.get_peers()

    immediate_create_group([p0, p1, p2, p3])

    with relay.queue_all_and_deliver(offline=[p3]):
        DelMemberMessage(p0, member=p2.id)

    # offline p3 sends a message with old memberlist and goes online
    with relay.queue_all_and_deliver():
        AddMemberMessage(p3, member=p4.id)

    # we need a chat message from a higher clock state to heal consistency
    with relay.queue_all_and_deliver():
        ChatMessage(p0)
    relay.assert_group_consistency()
    assert p0.members == set(["p0", "p1", "p3", "p4"])


def test_simple_removals_while_offline():
    relay = Relay(numpeers=7)
    p0, p1, p2, p3, p4, p5, p6 = relay.get_peers()

    immediate_create_group([p0, p1, p2, p3, p4, p5, p6])

    with relay.queue_all_and_deliver(offline=[p2, p3]):
        DelMemberMessage(p0, member=p5.id)
        DelMemberMessage(p1, member=p6.id)

    with relay.queue_all_and_deliver():
        pass
    relay.dump("all online again")
    relay.assert_group_consistency()


def test_removed_member_removes_another_while_offline():
    relay = Relay(numpeers=7)
    p0, p1, p2, p3, p4, p5, p6 = relay.get_peers()

    immediate_create_group([p0, p1, p2, p3, p4, p5, p6])

    with relay.queue_all_and_deliver(offline=[p5]):
        DelMemberMessage(p0, member=p5.id)
        DelMemberMessage(p5, member=p6.id)

    with relay.queue_all_and_deliver():
        ChatMessage(p0)

    relay.assert_group_consistency()
    assert p0.members == {"p0", "p1", "p2", "p3", "p4"}
