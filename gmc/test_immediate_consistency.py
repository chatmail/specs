import random
from gmc import (
    Relay,
    ChatMessage,
    AddMemberMessage,
    DelMemberMessage,
    immediate_create_group,
)

import pytest


@pytest.mark.parametrize(
    "n_actors,n_contacts,steps", [(2, 2, 20), (10, 50, 500), (20, 3, 500)]
)
def test_immediate_consistency(n_actors, n_contacts, steps):
    # Actors who are going to add/remove contacts
    # and send messages about this to each other.

    relay = Relay(n_actors + n_contacts)
    _peers = list(relay.get_peers())
    actors = list(_peers[:n_actors])
    contact_ids = set(x.id for x in _peers[n_actors:])

    immediate_create_group(actors)

    for _t in range(steps):
        # Select random actor.
        actor = random.choice(actors)

        for receive_from in actors:
            # Maybe receive a message or do nothing
            relay._drain_mailbox(actor, receive_from, num=random.randrange(2))

        if random.choice([True, False]):
            continue

        action = random.choice(["chat", "add", "remove"])
        if action == "chat":
            ChatMessage(actor)
        elif action == "add":
            possible_contacts = list(contact_ids.difference(actor.members))
            if possible_contacts:
                AddMemberMessage(actor, member=random.choice(possible_contacts))
        elif action == "remove":
            possible_contacts = list(contact_ids.intersection(actor.members))
            if possible_contacts:
                DelMemberMessage(actor, member=random.choice(possible_contacts))

    relay.receive_messages()
    relay.assert_group_consistency(peers=actors)
    # let one actor send a message to synchronize all contacts
    ChatMessage(actors[0])
    relay.receive_messages()

    relay.assert_group_consistency()
    relay.dump("something")
    print("algorithm achieved immediate consistency")
