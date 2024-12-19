#!/usr/bin/env python3
import random
import copy

# Actors who are going to add/remove contacts
# and send messages about this to each other.
n_actors = 3

n_contacts = 3

members = {actor: set() for actor in range(n_actors)}
clock = {actor: 0 for actor in range(n_actors)}
queues = {}
for r in range(n_actors):
    queues[r] = {s: [] for s in range(n_actors)}


def process_msg(r, msg):
    print(f"{r} received {msg}")

    if msg["clock"] > clock[r]:
        members[r] = set(msg["to"])
        clock[r] = msg["clock"]
    elif msg["action"] == "chat":
        if msg["clock"] == clock[r]:
            members[r].update(msg["to"])
            clock[r] += 1
    elif msg["action"] == "add":
        if msg["clock"] == clock[r]:
            if msg["member"] not in members[r]:
                members[r].add(msg["member"])
                clock[r] += 1
        else:
            members[r].add(msg["member"])
    elif msg["action"] == "remove":
        if msg["clock"] == clock[r]:
            if msg["member"] in members[r]:
                members[r].discard(msg["member"])
                clock[r] += 1
        else:
            members[r].discard(msg["member"])


for _t in range(1, 50):
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

    action = random.choice(["chat", "add", "remove"])

    if action == "chat":
        msg = {
            "action": "chat",
            "to": frozenset(members[actor]),
            "clock": clock[actor],
        }
    elif action == "add":
        possible_contacts = list(set(range(n_contacts)) - members[actor])
        if not possible_contacts:
            continue
        contact_id = random.choice(possible_contacts)

        print(f"{actor} adds {contact_id}")
        members[actor].add(contact_id)
        clock[actor] += 1
        msg = {
            "action": "remove",
            "to": frozenset(members[actor]),
            "clock": clock[actor],
            "member": contact_id,
        }
    elif action == "remove":
        if not members[actor]:
            continue
        contact_id = random.choice(list(members[actor]))

        print(f"{actor} removes {contact_id}")
        members[actor].discard(contact_id)
        clock[actor] += 1
        msg = {
            "action": "remove",
            "to": frozenset(members[actor]),
            "clock": clock[actor],
            "member": contact_id,
        }
    for r in range(n_actors):
        if r != actor:
            queues[r][actor].insert(0, msg)


# Read remaining messages.
for r in range(n_actors):
    for s in range(n_actors):
        while len(queues[r][s]) > 0:
            msg = queues[r][s].pop()
            print(f"{r} received msg from {s}")
            process_msg(r, msg)


for actor in range(n_actors - 1):
    print(members[actor])
    assert members[actor] == members[actor + 1]
