#!/usr/bin/env python3
import random
import copy

# Actors who are going to add/remove contacts
# and send messages about this to each other.
n_actors = 20

n_contacts = 10

# Member list for each actor.

# Member list is a dictionary
# with contact ID as a key and a pair of timestamp and boolean.
# Boolean is true if contact is a member,
# otherwise it's a tombstone for removed member.
members = {
    actor: {contact_id: (0, False) for contact_id in range(n_contacts)}
    for actor in range(n_actors)
}
queues = {}
for r in range(n_actors):
    queues[r] = {s: [] for s in range(n_actors)}


def process_msg(r, msg):
    print(f"{r} received {msg}")
    for contact_id in range(n_contacts):
        (ts, is_member) = members[r][contact_id]
        if msg[contact_id][0] > ts:
            members[r][contact_id] = copy.deepcopy(msg[contact_id])


for clock in range(1, 500):
    # Select random actor.
    actor = random.randrange(n_actors)

    # Maybe receive messages.
    for s in range(n_actors):
        if queues[actor][s]:
            if random.randrange(2) == 1:
                msg = queues[actor][s].pop()
                print(f"{actor} received msg from {s}")
                process_msg(actor, msg)

    if random.randrange(2) == 1:
        continue

    # Select random contact.
    contact_id = random.randrange(n_contacts)
    _ts, is_member = members[actor][contact_id]

    if is_member:
        # Remove contact
        print(f"{actor} removes {contact_id}")
        members[actor][contact_id] = (clock, False)
    else:
        # Add contact
        print(f"{actor} adds {contact_id}")
        members[actor][contact_id] = (clock, True)

    msg = copy.deepcopy(members[actor])
    for r in range(n_actors):
        if r != actor:
            print(f"{actor} sends msgs to {r}")
            queues[r][actor].insert(0, msg)

# Read remaining messages.
for r in range(n_actors):
    for s in range(n_actors):
        while len(queues[r][s]) > 0:
            msg = queues[r][s].pop()
            print(f"{r} received msg from {s}")
            process_msg(r, msg)


def member_set(actor):
    return set(
        contact_id for contact_id in range(n_contacts) if members[actor][contact_id][1]
    )


for actor in range(n_actors - 1):
    assert member_set(actor) == member_set(actor + 1)
