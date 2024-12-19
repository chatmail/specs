import contextlib


class Relay:
    def __init__(self, numpeers):
        self.peers = {}
        for i in range(numpeers):
            newpeer = Peer(relay=self, num=i)
            self.peers[newpeer.id] = newpeer

    def get_peers(self):
        return self.peers.values()

    def dump(self, title):
        print()
        print("#")
        print(f"# {title}")
        print("#")
        for peer_id, peer in self.peers.items():
            pending = sum(len(x) for x in peer.from2mailbox.values())
            members = ",".join(sorted(peer.members))
            off = " [OFFLINE]" if peer in self.offline_peers else ""
            print(f"{peer_id} clock={peer.clock} members={members} {off}")
            for sender, pending in peer.from2mailbox.items():
                for msg in pending:
                    print(f"   {sender.id} {msg}")
        print()

    @contextlib.contextmanager
    def queue_all_and_deliver(self, offline=None):
        self.offline_peers = set(offline) if offline else set()
        print("## Queuing messages")
        yield
        self.dump("before message delivery")
        self._receive_all()
        self.dump("after message delivery")
        self.offline_peers.clear()

    def _receive_all(self):
        for peer in self.peers.values():
            if peer in self.offline_peers:
                continue
            for from_peer in self.peers.values():
                if from_peer in self.offline_peers:
                    continue
                # drain peer mailbox by reading messages from each sender separately
                for msg in peer.from2mailbox.pop(from_peer, []):
                    assert peer.id != from_peer.id
                    receive_func = globals()[f"Receive{msg.typ}"]
                    print(f"receive {peer}")
                    print(f"    msg {msg}")
                    receive_func(peer, msg)
                    print(f"    new {peer}")

    def assert_group_consistency(self):
        peers = list(self.peers.values())
        for peer1, peer2 in zip(peers, peers[1:]):
            assert peer1.members == peer2.members
            assert peer1.clock == peer2.clock
            nums = ",".join(sorted(peer1.members))
            print(f"{peer1.id} and {peer2.id} have same members {nums}")

    def queue_message(self, msg):
        assert isinstance(msg, ChatMessage)
        print(f"queueing {msg}")
        for peer_id in msg.recipients:
            peer = self.peers[peer_id]
            if peer_id == msg.sender.id:
                continue  # we don't send message to ourselves
            # serialize message for each distinct peer
            msgdict = dict(
                typ=msg.__class__.__name__,
                recipients=msg.recipients.copy(),
                clock=msg.clock,
                payload=msg.payload.copy(),
            )
            # provide per-sender buckets to allow modeling offline-ness for peers
            peer_mailbox = peer.from2mailbox.setdefault(msg.sender, [])
            # create a distinct message object for each receiving peer
            incoming_msg = IncomingMessage(sender_id=msg.sender.id, msgdict=msgdict)
            peer_mailbox.append(incoming_msg)


class Peer:
    def __init__(self, relay, num):
        self.relay = relay
        self.id = f"p{num}"
        self.members = set()
        self.from2mailbox = {}
        self.clock = 0

    def __eq__(self, other):
        return self.id == other.id

    def __hash__(self):
        return int(self.id[1:])

    def __repr__(self):
        clock = self.clock
        members = sorted(self.members)
        return f"{self.id} members={','.join(members)} c={clock}"


class IncomingMessage:
    def __init__(self, sender_id, msgdict):
        self.sender_id = sender_id
        self.__dict__.update(msgdict)

    def __repr__(self):
        abbr = f"{self.typ}({self.payload.get('member', '')})"
        rec = ",".join(sorted(self.recipients))
        return f"from={self.sender_id} to={rec} c={self.clock} {abbr}"


def immediate_create_group(peers):
    for peer in peers:
        assert peer.clock == 0
        assert not peer.members
        peer.clock = 1
        peer.members = set([x.id for x in peers])


#
# Add/Del/Regular chat messages used for sending/queuing
#


class ChatMessage:
    def __init__(self, sender, **payload):
        self.sender = sender
        self.payload = payload
        self.before_send()
        self.recipients = frozenset(self.sender.members)
        self.clock = self.sender.clock
        self.sender.relay.queue_message(self)
        self.after_send()

    def __repr__(self):
        nums = ",".join(self.sender.members)
        name = self.__class__.__name__
        return f"<{name} clock={self.clock} {self.sender.id}->{nums} {self.payload}>"

    def before_send(self):
        pass

    def after_send(self):
        pass


class AddMemberMessage(ChatMessage):
    def before_send(self):
        self.sender.members.add(self.payload["member"])
        self.sender.clock += 1


class DelMemberMessage(ChatMessage):
    def before_send(self):
        self.sender.clock += 1

    def after_send(self):
        self.sender.members.remove(self.payload["member"])


# Receiving Chat/Add/Del messages


def ReceiveChatMessage(peer, msg):
    assert peer.id in msg.recipients

    reset_peer_if_older(peer, msg)

    if peer.clock == msg.clock and peer.members != sender_members(msg):
        print(f"{peer.id} has different members than incoming same-clock message")
        print(f"{peer.id} merging message recipients, and increase own clock")
        peer.members.update(sender_members(msg))
        peer.clock = msg.clock + 1


def ReceiveAddMemberMessage(peer, msg):
    assert peer.id in msg.recipients

    reset_peer_if_older(peer, msg)

    peer.members.add(msg.payload["member"])

    inc_peer_clock_if_member_mismatch(peer, msg)


def ReceiveDelMemberMessage(peer, msg):
    assert peer.id in msg.recipients

    if peer.clock < msg.clock:
        peer.members = set(sender_members(msg))
        peer.clock = msg.clock
    elif msg.payload["member"] in peer.members:
        peer.members.discard(msg.payload["member"])
        peer.clock += 1


def sender_members(msg):
    if msg.typ == "DelMemberMessage":
        return msg.recipients - {msg.payload["member"]}
    else:
        return msg.recipients


def inc_peer_clock_if_member_mismatch(peer, msg):
    if peer.clock == msg.clock and peer.members != sender_members(msg):
        peer.clock += 1


def reset_peer_if_older(peer, msg):
    if peer.clock < msg.clock:
        print(f"{peer.id} is outdated, setting peer.members to msg.recipients")
        peer.members = set(sender_members(msg))
        peer.clock = msg.clock
