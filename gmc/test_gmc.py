import itertools

import gmc
from gmc import (
    immediate_create_group,
    AddMemberMessage,
    DelMemberMessage,
    ChatMessage,
    Relay,
)

import pytest


@pytest.fixture(autouse=True)
def override_time(monkeypatch):
    count = itertools.count()

    def pseudo_current_timestamp():
        return 100 + next(count)

    monkeypatch.setattr(gmc, "current_timestamp", pseudo_current_timestamp)


def test_add_and_remove():
    relay = Relay(numpeers=4)
    p0, p1, p2, p3 = relay.get_peers()

    # create group
    immediate_create_group([p0, p1])
    assert p0.members == p1.members == set([p0.id, p1.id])

    # add members
    AddMemberMessage(p0, member=p2.id)
    AddMemberMessage(p0, member=p3.id)
    relay.receive_messages()
    relay.assert_group_consistency()

    # del member
    DelMemberMessage(p3, member=p0.id)
    relay.receive_messages()
    relay.assert_group_consistency()


def test_concurrent_add():
    relay = Relay(numpeers=4)
    p0, p1, p2, p3 = relay.get_peers()

    immediate_create_group([p0, p1])

    # concurrent addition of two group members
    AddMemberMessage(p1, member=p2.id)
    AddMemberMessage(p0, member=p3.id)
    relay.receive_messages()

    # p0 and p1 know now of each others additions
    # so need to send a message to get overall consistent membership
    ChatMessage(p0)
    relay.receive_messages()

    relay.assert_group_consistency()


def test_concurrent_delete():
    relay = Relay(numpeers=4)
    p0, p1, p2, p3 = relay.get_peers()

    immediate_create_group([p0, p1, p2, p3])

    # concurrent deletion of two group members
    DelMemberMessage(p1, member=p2.id)
    DelMemberMessage(p0, member=p3.id)
    relay.receive_messages()

    # p0 and p1 know now of each others additions
    # so need to send a message to get overall consistent membership
    ChatMessage(p0)
    relay.receive_messages()

    relay.assert_group_consistency()
    assert p0.members == set(["p0", "p1"])


def test_add_remove_and_stale_member_sends_chatmessage():
    relay = Relay(numpeers=4)
    p0, p1, p2, p3 = relay.get_peers()

    immediate_create_group([p0, p1, p2, p3])

    # p0 deleted p2 while p3 is offline
    DelMemberMessage(p0, member=p2.id)
    relay.receive_messages(notreceive=[p3])

    # offline p3 sends a message with old memberlist and goes online
    ChatMessage(p3)
    relay.receive_messages()

    relay.assert_group_consistency()

    ChatMessage(p0)
    relay.receive_messages()

    assert p0.members == set(["p0", "p1", "p3"])


def test_add_remove_and_stale_member_sends_addition():
    relay = Relay(numpeers=5)
    p0, p1, p2, p3, p4 = relay.get_peers()

    immediate_create_group([p0, p1, p2, p3])

    DelMemberMessage(p0, member=p2.id)
    relay.receive_messages(notreceive=[p3])

    # offline p3 sends a message with old memberlist and goes online
    AddMemberMessage(p3, member=p4.id)
    relay.receive_messages()

    # we need a chat message from a higher clock state to heal consistency
    ChatMessage(p0)
    relay.receive_messages()

    relay.assert_group_consistency()
    assert p0.members == set(["p0", "p1", "p3", "p4"])


def test_simple_removals_while_offline():
    relay = Relay(numpeers=7)
    p0, p1, p2, p3, p4, p5, p6 = relay.get_peers()

    immediate_create_group([p0, p1, p2, p3, p4, p5, p6])

    DelMemberMessage(p0, member=p5.id)
    DelMemberMessage(p1, member=p6.id)
    relay.receive_messages(notreceive=[p2, p3])

    relay.receive_messages()
    relay.dump("all online again")
    relay.assert_group_consistency()


def test_removed_member_removes_another_while_offline():
    relay = Relay(numpeers=7)
    p0, p1, p2, p3, p4, p5, p6 = relay.get_peers()

    immediate_create_group([p0, p1, p2, p3, p4, p5, p6])

    DelMemberMessage(p0, member=p5.id)
    DelMemberMessage(p5, member=p6.id)
    relay.receive_messages(notreceive=[p5])

    ChatMessage(p0)
    relay.receive_messages()

    relay.assert_group_consistency()
    assert p0.members == {"p0", "p1", "p2", "p3", "p4"}
    relay.dump("123")


def test_stale_member():
    relay = Relay(numpeers=3)
    p1, p2, p3 = relay.get_peers()

    immediate_create_group([p1])

    AddMemberMessage(p1, member=p2.id)
    relay.receive_messages()

    DelMemberMessage(p1, member=p2.id)
    DelMemberMessage(p1, member=p1.id)

    AddMemberMessage(p2, member=p3.id)

    # Now p3 has {p1, p2, p3} as members,
    # but p1 and p2 think they succesfully left the group.
    relay.receive_messages()

    # This check fails.
    relay.assert_group_consistency()
