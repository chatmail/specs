# Modeling group membership

We simulate managing group membership
of a single group chat.
Initially the chat is created on some
arbitrary device.

Devices interact by sending messages.
Each message contains the set of recipients
(`To:` header) and the set of old recipients prior to sending the message.
In Delta Chat there is no header to send the list of old recipients,
but it can be derived from the `To:` header
by removing the member if it is listed in `Chat-Group-Member-Added` header
or adding it if it is listed in the `Chat-Group-Member-Removed` header.
We do not consider non-chat messages,
for them we can assume that old list of recipients is the same
as our current member list.

## TLA+ model

TLA+ model is stored in `groupmembership.tla`.

Constraints are defined in the model instance stored in `MC.tla`
and corresponding TLC configuration is in `MC.cfg`.

The model can be checked using [TLC model checker](https://github.com/tlaplus/tlaplus)
by running `tlc MC.tla`.

## Assumptions

1. Devices send messages to each other over reliable FIFO channels.

   In practice they send messages to the submission port of SMTP server
   which then delivers them to inboxes of recipient devices
   and recipient devices read messages from inboxes over IMAP at their own pace.

   We assume no reordering happens within one FIFO channel,
   i.e. between two devices, but for different sender devices
   and single recipient device messages can be interleaved.

   In practice messages can be reordered by SMTP server
   because on temporary error message is postponed
   and another message that was sent later may be delivered first.
   Postfix+Dovecot server sometimes does this reordering even within
   a single machine. We ignore such reordering for simplicity.

   Note that some device may ignore messages from another device
   for the whole run and only read them at the very end,
   which is almost as bad as having a blocked contact.
   Even worse, the messages are received eventually
   and device should get into the same state as everyone else
   after processing them.

2. There is a global clock available
   that can be used to produce timestamps that can be
   sent between devices.

   Such clock can be implemented as a logical clock,
   i.e. Lamport timestamps or vector clocks.
   In practice we use wall clock
   which is good enough if users don't
   modify the group at exactly the same second.

   This assumption can be modeled by
   having a strict total order relation
   on all messages ever sent.

3. There are no malicious devices.

   For example, if some device A is removed from the group,
   it can backdate the message saying it has added device B to the group
   and from device B send a message saying it has removed everyone from the group
   before device A was removed, effectively destroying the group.

   We assume no device is going to do such attack.
   Some security mechanism can be bolted on later,
   like ignoring messages from non-member devices
   if they appear to arrive significantly late,
   but we ignore it in the model.

   There are anyway multiple ways to break groups,
   like deliberately
   sending control messages only to a subset of members
   or creating another group with the same ID
   but another memberlist, overlapping with the real one
   only partially.

   Security of Delta Chat groups relies on the fact
   that attackers do not know the group ID
   it is better to create a new group if there is
   a need to get rid of a malicious user.

4. We do not explicitly model multi-device setups.

   If multiple devices share the same address
   they will be added and removed simultaneously
   and will receive messages from different FIFO queues
   in the same order,
   but these are just additional constraints on the simulation runs.

## Requirements

### Eventual consistency

We want a protocol that results
in all devices that think they are part of the member list
to eventually converge to the same member list
given the following conditions:

1. All devices that think they are members of the group
   keep sending messages to the group.

   Otherwise it is possible that
   A adds B to the chat,
   then B adds C and A adds D concurrently.
   Eventually when all messages are delivered,
   only B learns that D was added
   and C never gets the message that D is added as A sends it only to B.
   A or B should send a message to the chat
   to tell C that D is now a member of the group.

   In practice inactive members are removed eventually
   because their account runs over quota and results in errors,
   or we don't care that their member list
   does not converge to the same state as for other devices.
   We should test that such devices don't revert
   member list to some very old state if they decide
   to send a message, but this requirement is difficult to formalize.

2. All devices eventually stop sending membership messages that change member list.

### Immediate consistency

If subset of devices S has empty reception queues
and the same view of the group memberlist
and later always only modifies membership of devices outside the state S,
then whenever devices in the set S have empty reception queues
they have the same group memberlist.

Less formally, as long as membership of some device is not modified,
fetching all messages should be enough to get into state consistent
with other similar devices.

## State transitions

Initially there is one device
that created the chat and has itself in the member list
and all other devices have empty member list.

The following state transitions can happen during the simulation:

1. Device that thinks it is currently a member
   adds another device to the chat.

   It adds new device to its local member list
   and sends "Member added" message
   to all devices in the new member list
   by adding it to FIFO channels of all chat members.

2. Device that thinks it is currently a member
   removes a member (possibly self) from the chat.

   It removes a device from its local member list
   and sends a "Member removed" message
   to all devices in the old member list.

3. Device sends a chat message to the group.

4. Device reads one message from one of its FIFO channels.

# Algorithm

Each device maintains a logical clock for the chat.
Clock value is initialized to 0.

Current clock value is included in each message
together with the new member list.

When device adds or removes a member,
it increases the clock by 1 before sending the message.

When receiving a chat message,
receiver compares its clock value
with the message clock.

If clock value in the message
is higher than the receiver clock value,
receiver sets the clock with the value from the message
and replaces its local member list
with the member list from the message.

If clock value in the message
is lower than the receiver clock value,
then the receier ignores the message
and keeps its own clock value and member list.

If clock value in the message
is the same as the receiver clock value,
receiver updates its own member list
with the member list from the message
by taking an union of the member lists
and increases its clock by 1.

TODO: specify processing of "Member added"
and "Member removed" messages.
