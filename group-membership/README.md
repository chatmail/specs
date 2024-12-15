# Modeling group membership

Assumptions:

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

We simulate a single group chat
as group chats are independent.
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

Initially there is one device
that created the chat and has itself in the member list
and all other devices have empty member list.

The following state transitions can happen during the simulation:

1. Device that thinks it is currently a member
   of the chat sends a message,
   adding it to FIFO channels of all chat members.

   It changes its member list to the new value.
   New member list has no restrictions,
   it can add or remove any members, including the sending device
   so device can leave the group.

   If device is just chatting,
   it sends a message with the same new and old member list.

2. Device reads one message from one of its FIFO channels.
