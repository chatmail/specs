from datetime import datetime
import itertools
from pprint import pprint


def current_timestamp():
    return datetime.utcnow().timestamp()


def lsformat(members):
    """format a sorted list of peer ids into a ',' separated string"""
    l = map(lambda x: x if isinstance(x, str) else x.id, members)
    return ",".join(sorted(l, key=lambda x: int(x[1:])))


def lcformat(lastchanged):
    l = []
    for peer_id in sorted(lastchanged):
        l.append(f"{peer_id}->{lastchanged[peer_id]}")
    return ", ".join(l)


class Relay:
    def __init__(self, numpeers):
        self.count_receive_messages_calls = itertools.count()
        self.peers = {}
        self.notify_stale = []
        for i in range(numpeers):
            newpeer = Peer(relay=self, num=i)
            self.peers[newpeer.id] = newpeer

    def get_peers(self):
        return self.peers.values()

    def dump(self, title):
        print(f"{title}")
        for peer_id, peer in self.peers.items():
            pending = sum(len(x) for x in peer.from2mailbox.values())
            print(peer)
            for sender, pending in peer.from2mailbox.items():
                for msg in pending:
                    print(f"   {sender.id} {msg}")

    def receive_messages(self, notreceive=None, notfrom=None):
        """receive messages on all 'peers' (all if not specified)
        except from 'notfrom' peers where messages are kept pending."""
        notreceive = set(notreceive) if notreceive else set()
        notfrom = set(notfrom) if notfrom else set()

        count = next(self.count_receive_messages_calls)
        title = f"# [{count}] BEGIN RECEIVING MESSAGES"
        if notreceive:
            title += f" notreceive={lsformat(notreceive)}"
        if notfrom:
            title += f" notfrom={lsformat(notfrom)}"

        print(title)
        for peer, from_peer in itertools.product(self.get_peers(), self.get_peers()):
            if from_peer not in notfrom and peer not in notreceive:
                self._drain_mailbox(peer, from_peer)
        self.dump(f"# [{count}] PROCESSED INCOMING MESSAGES, PEERSTATES:")
        if self.notify_stale:
            print("# notify peers who send us a message even though we left the group")
            while self.notify_stale:
                peer, stale_member = self.notify_stale.pop()
                RetryLeave(peer, recipients=[stale_member])
        print(f"# [{count}] FINISH RECEIVING MESSAGES")

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
            print(f"before {peer}")
            print(f"   msg {msg}")
            update_peer_from_incoming_message(peer, msg)
            print(f" after {peer}")

    def assert_group_consistency(self, peers=None):
        if peers is None:
            peers = list(x for x in self.peers.values() if x.id in x.members)

        # checking that actors do not contain peers who themselves think they are not members
        left_peers = list(x.id for x in self.peers.values() if x.id not in x.members)
        for peer in peers:
            assert not peer.members.intersection(left_peers)

        # checking that all peers have the same member list
        ok = True
        for peer1, peer2 in zip(peers, peers[1:]):
            if peer1.members == peer2.members:
                nums = lsformat(peer.members)
                print(f"{peer1.id} and {peer2.id} have same members {nums}")
            else:
                print(f"Peers member mismatch {peer1.id}.members != {peer2.id}.members")
                print(peer1)
                print(peer2)
                print()
                ok = False

        assert ok, "peers differ"

    def queue_message(self, msg, recipients=None):
        assert isinstance(msg, ChatMessage)
        print(f"queueing {msg}")
        if recipients is None:
            recipients = msg.recipients

        for peer_id in recipients:
            if peer_id == msg.sender.id:
                continue  # we don't send message to ourselves

            # create a distinct message object for each receiving peer
            incoming_msg = IncomingMessage(
                sender_id=msg.sender.id,
                msgdict=dict(
                    typ=msg.__class__.__name__,
                    recipients=msg.recipients.copy(),
                    lastchanged=msg.lastchanged.copy(),
                    member=msg.member,
                ),
            )
            # provide per-sender buckets to allow modeling offline-ness for peers
            peer = self.peers[peer_id]
            peer_mailbox = peer.from2mailbox.setdefault(msg.sender, [])
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
        lc = lcformat(self.lastchanged)
        return f"{self.id} members={lsformat(self.members)} lastchanged={{{lc}}}"


class IncomingMessage:
    def __init__(self, sender_id, msgdict):
        self.sender_id = sender_id
        self.__dict__.update(msgdict)

    def __repr__(self):
        rec = ",".join(sorted(self.recipients))
        lc = lcformat(self.lastchanged)
        name = self.typ
        if self.member:
            name += f"({self.member})"
        return f"{name} from={self.sender_id} to={rec} lastchanged={lc}"


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
    def __init__(self, sender, member=None, recipients=None):
        self.sender = sender
        assert self.__class__ in (ChatMessage, RetryLeave) or member is not None
        self.member = member
        self.before_send()
        self.lastchanged = sender.lastchanged.copy()
        self.recipients = self.sender.members.copy()
        self.sender.relay.queue_message(self, recipients=recipients)
        self.after_send()

    def __repr__(self):
        members = lsformat(self.sender.members)
        name = "Incoming" + self.__class__.__name__
        if self.member:
            name += f"({self.member})"
        return f"<{name} from={self.sender.id} to={members}>"

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


class RetryLeave(ChatMessage):
    """Updating timestamps for a peer who sends us message but we are not part of the group. """


# Receiving Chat/Add/Del/RetryLeave messages
# each of which can cause group membership updates


def update_peer_from_incoming_message(peer, msg):
    stale_timestamps = False
    for historic_peer, msg_lastchanged in msg.lastchanged.items():
        current_lastchanged = peer.lastchanged.get(historic_peer, 0)
        if current_lastchanged < msg_lastchanged:
            # the message contains newer information about this member
            peer.lastchanged[historic_peer] = msg_lastchanged

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
        elif current_lastchanged > msg_lastchanged:
            if peer.id not in peer.members and peer.id == historic_peer:
                # we are no longer in the group (we left or got removed)
                # and we have a newer timestamp for ourselves
                stale_timestamps = True

    if stale_timestamps:
        peer.relay.notify_stale.append((peer, msg.sender_id))
