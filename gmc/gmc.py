from datetime import datetime
import itertools
from pprint import pprint


def current_timestamp():
    return datetime.utcnow().timestamp()


class Relay:
    def __init__(self, numpeers):
        self.peers = {}
        for i in range(numpeers):
            newpeer = Peer(relay=self, num=i)
            self.peers[newpeer.id] = newpeer

    def get_peers(self):
        return self.peers.values()

    def dump(self, title):
        for peer_id, peer in self.peers.items():
            pending = sum(len(x) for x in peer.from2mailbox.values())
            members = ",".join(sorted(peer.members))
            print(f"{peer_id} members={members}")
            pprint(f"{peer.lastchanged}")
            for sender, pending in peer.from2mailbox.items():
                for msg in pending:
                    print(f"   {sender.id} {msg}")
        print()

    def receive_messages(self, notreceive=None, notfrom=None):
        """receive messages on all 'peers' (all if not specified)
        except from 'notfrom' peers where messages are kept pending."""
        notreceive = set(notreceive) if notreceive else set()
        notfrom = set(notfrom) if notfrom else set()

        print("# BEGIN RECEIVING MESSAGES")
        print(f"# notreceive={sorted([p.id for p in notreceive])}")
        print(f"# notfrom={[p.id for p in notfrom]}")
        for peer, from_peer in itertools.product(self.get_peers(), self.get_peers()):
            if from_peer not in notfrom and peer not in notreceive:
                self._drain_mailbox(peer, from_peer)
        print("# FINISH RECEIVING MESSAGES")
        print()

    def _drain_mailbox(self, peer, from_peer, num=-1):
        # drain peer mailbox by reading messages from each sender separately
        while num != 0:
            queue = peer.from2mailbox.get(from_peer, [])
            if not queue:
                peer.from2mailbox.pop(from_peer, None)
                break
            num = num - 1
            msg = queue.pop(0)
            assert peer.id != from_peer.id, "messages sent to self not supported"
            print(f"receive {peer}")
            print(f"    msg {msg}")
            update_peer_from_incoming_message(peer, msg)
            print(f"    new {peer}")

    def assert_group_consistency(self):
        peers = list(x for x in self.peers.values() if x.id in x.members)
        ok = True
        for peer1, peer2 in zip(peers, peers[1:]):
            if peer1.members == peer2.members:
                nums = ",".join(sorted(peer1.members, key=lambda x: int(x[1:])))
                print(f"{peer1.id} and {peer2.id} have same members {nums}")
            else:
                print(f"Peers member mismatch {peer1.id}.members != {peer2.id}.members")
                print(peer1)
                print(peer2)
                print()
                ok = False

        assert ok, "peers differ"

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
                lastchanged=msg.lastchanged.copy(),
                member=msg.member,
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
        # dict which maps past/present members to timestamp
        self.lastchanged = {}

    def __eq__(self, other):
        return self.id == other.id

    def __hash__(self):
        return int(self.id[1:])

    def __repr__(self):
        members = sorted(self.members, key=lambda x: int(x[1:]))
        return f"{self.id} members={','.join(members)}"


class IncomingMessage:
    def __init__(self, sender_id, msgdict):
        self.sender_id = sender_id
        self.__dict__.update(msgdict)

    def __repr__(self):
        abbr = f"{self.typ}({self.member})"
        rec = ",".join(sorted(self.recipients))
        num_lastchanged = len(self.lastchanged)
        return (
            f"from={self.sender_id} to={rec} num_lastchanged={num_lastchanged} {abbr}"
        )


def immediate_create_group(peers):
    for peer in peers:
        assert not peer.members
        peer.members = set([x.id for x in peers])
        now = current_timestamp()
        for peer in peers:
            peer.lastchanged = dict((p.id, now) for p in peers)


#
# Add/Del/Regular chat messages used for sending/queuing
#


class ChatMessage:
    def __init__(self, sender, member=None):
        self.sender = sender
        assert self.__class__ == ChatMessage or member is not None
        self.member = member
        self.before_send()
        self.lastchanged = sender.lastchanged.copy()
        self.recipients = frozenset(self.sender.members)
        self.sender.relay.queue_message(self)
        self.after_send()

    def __repr__(self):
        members = ",".join(self.sender.members)
        name = self.__class__.__name__
        return f"<{name} {self.sender.id}->{members} {self.member}>"

    def before_send(self):
        pass

    def after_send(self):
        pass


class AddMemberMessage(ChatMessage):
    def before_send(self):
        self.sender.members.add(self.member)
        self.sender.lastchanged[self.member] = current_timestamp()


class DelMemberMessage(ChatMessage):
    def before_send(self):
        self.sender.lastchanged[self.member] = current_timestamp()

    def after_send(self):
        self.sender.members.remove(self.member)


# Receiving Chat/Add/Del messages


def update_peer_from_incoming_message(peer, msg):
    assert peer.id in msg.recipients

    for historic_peer, lastchanged in msg.lastchanged.items():
        if peer.lastchanged.get(historic_peer, 0) < lastchanged:
            # the message contains newer information about this member
            peer.lastchanged[historic_peer] = lastchanged

            if historic_peer == msg.member:
                if msg.typ == "DelMemberMessage":
                    peer.members.discard(historic_peer)
                elif msg.typ == "AddMemberMessage":
                    peer.members.add(historic_peer)
            elif historic_peer not in msg.recipients and historic_peer in peer.members:
                print(f"implicititely removing {historic_peer}")
                peer.members.remove(historic_peer)
            elif historic_peer in msg.recipients and historic_peer not in peer.members:
                print(f"implicititely adding {historic_peer}")
                peer.members.add(historic_peer)
