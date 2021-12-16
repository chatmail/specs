----------------------------- MODULE deltachat -----------------------------

(***************************************************************************)
(* Model of a single IMAP server and multiple devices.                     *)
(*                                                                         *)
(* Devices fetch the messages and move them from the Inbox folder to       *)
(* the Movebox folder on the server.                                       *)
(***************************************************************************)

EXTENDS Naturals \* We need naturals for `^UIDs.^'

\* Running for more than two devices or messages is really slow.
CONSTANT Devices, \* Symmetry set of devices such as `{d1, d2}'.
         MessageIds \* Symmetry set of Message-IDs such as `{m1, m2}'.

VARIABLES Storage, \* The set of messages in the server folders.
          UidNext, \* `^UID^' that will be assigned to the next message in a folder.
          ExpectedUid, \* Function from folder to the next expected `^UID.^'
          SentMessages,(****************************************************)
                       (* The set of Message-IDs that have been sent and   *)
                       (* may eventually arrive into the Inbox.            *)
                       (****************************************************)
          ReceivedMessages, \* The set of Message-IDs downloaded by the devices.
          ImapTable \* Device view of the IMAP server state.

(* The server has two folders: Inbox and Movebox. *)
Folders ==
  {"inbox", "movebox"}

(* The set of possible records on the server. *)
StorageRecords ==
  [uid : Nat \ {0}, messageId : MessageIds, seen: BOOLEAN]

(* The set of possible records in the relational database on the device.
   Note that there may be multiple records for the same Message-ID
   if the message was seen both in the Inbox and Movebox. *)
ImapRecords ==
  [messageId: MessageIds,
   uid: Nat \ {0},
   folder: Folders,
   delete: BOOLEAN] \* Whether the message must be deleted.

----------------------------------------------------------------------------

TypeOK ==
  /\ Storage \in [Folders -> SUBSET StorageRecords]
  /\ \A f \in Folders : \* UIDs in each folder are unique.
     \A m1, m2 \in Storage[f] : m1 /= m2 => m1.uid /= m2.uid
  /\ UidNext \in [Folders -> Nat \ {0}]
  /\ ExpectedUid \in [Devices -> [Folders -> Nat]]
  /\ SentMessages \subseteq MessageIds
  /\ ReceivedMessages \in [Devices -> SUBSET MessageIds]
  /\ ImapTable \in [Devices -> SUBSET ImapRecords]
  /\ \A d \in Devices :
     \A r1, r2 \in ImapTable[d] : \* Uniqueness constraint.
     (r1.folder = r2.folder /\ r1.uid = r2.uid) => r1 = r2

Init ==
  /\ Storage = [f \in Folders |-> {}]
  /\ UidNext = [f \in Folders |-> 1]
  /\ ExpectedUid = [d \in Devices |-> [f \in Folders |-> 0]]
  /\ SentMessages = MessageIds
  /\ ReceivedMessages = [d \in Devices |-> {}]
  /\ ImapTable = [d \in Devices |-> {}]

----------------------------------------------------------------------------

(* Server has not been changed. Sent messages are not part of the server state,
   but we include the set of sent messages because the only way it can change
   is by the message being delivered to the server *)
ServerUnchanged ==
  UNCHANGED <<Storage,
              UidNext,
              SentMessages>>

----------------------------------------------------------------------------

(* A message with Message-ID `m' arrives into the Inbox folder. *)
MessageArrives(m) ==
  /\ m \in SentMessages \* This message has never arrived yet.
  /\ Storage' = [Storage EXCEPT !["inbox"] = Storage["inbox"] \union
                                {[uid |-> UidNext["inbox"],
                                  messageId |-> m,
                                  seen |-> FALSE]}]
  /\ UidNext' = [UidNext EXCEPT !["inbox"] = UidNext["inbox"] + 1]
  /\ SentMessages' = SentMessages \ {m}
  /\ UNCHANGED <<ExpectedUid, ReceivedMessages, ImapTable>>

(* Each device may FETCH from the folder at any time.
This includes the case when the device always fetches at the right time,
so we don't need to model the IDLE protocol.
We also don't model separate FETCH request and response.
Instead, FETCH operation makes the device aware of all the new messages since the last seen UID
and updates the last seen UID to the UID next.
The device gets no information about whether the messages it fetched previously are deleted.
*)

(* Device d fetches the messages from the f folder.
   Duplicate messages are marked for deletion.
   TODO: mark message in Inbox for deletion if there is a copy in the Movebox already.
 *)
FetchFolder(d, f) ==
  LET
    NewMessages == {x \in Storage[f] : x.uid >= ExpectedUid[d][f]}
  IN
  /\ ExpectedUid' = [ExpectedUid EXCEPT ![d][f] = UidNext[f]]
  /\ UNCHANGED ReceivedMessages
  /\ ServerUnchanged
  /\ ImapTable' = [ImapTable EXCEPT ![d] =
       ImapTable[d] \union
         {[uid |-> r.uid,
           messageId |-> r.messageId,
           folder |-> f,
           delete |-> \/ \E x \in ImapTable[d] : x.folder = f /\
                                                 x.messageId = r.messageId /\
                                                 x.delete = FALSE
                      \/ \E x \in NewMessages : x.uid < r.uid /\
                                                x.messageId = r.messageId
           ] : r \in NewMessages }]

(* Fetch message contents. *)
\* TODO: replace with downloading of a single message with minimal UID that is not downloaded yet.
PullFolder(d, f) ==
  LET
    RequestedRecords ==
      {r \in ImapTable[d] : /\ r.folder = f
                            /\ (r.messageId \notin ReceivedMessages[d]) }
    RequestedUids == {r.uid : r \in RequestedRecords}
    PulledMessages == {x \in Storage[f] : x.uid \in RequestedUids}
    PulledMessageIds == {x.messageId : x \in PulledMessages}
  IN
  /\ ServerUnchanged
  /\ UNCHANGED <<ImapTable, ExpectedUid>>
  /\ ReceivedMessages' =
       [ReceivedMessages EXCEPT ![d] = ReceivedMessages[d] \union PulledMessageIds]

(* Device `d' successfully moves the message with UID `uid' from the Inbox to the Movebox.
   Note that there is no check that the message being moved has the Message-ID that the device
   thinks is stored under this UID. If ImapTable is incorrect, it is possible
   to successfully move the wrong message.

   After moving, UIDs are assumed to be unknown, so no record is added.
   IMAP4rev2 (RFC 9051) supports COPYUID, but we assume IMAP4rev1 (RFC 3501) here. *)
MoveMessageSuccess(d, inboxRecord) ==
  \E r \in Storage["inbox"] :
    /\ r.uid = inboxRecord.uid \* The message actually exists in the Inbox folder.
    /\ Storage' =
         [Storage EXCEPT !["inbox"] = Storage["inbox"] \ {r},
                         !["movebox"] = Storage["movebox"] \union
                           {[uid |-> UidNext["movebox"],
                             messageId |-> r.messageId,
                             seen |-> r.seen]}]
    /\ UidNext' = [UidNext EXCEPT !["movebox"] = UidNext["movebox"] + 1]
    /\ ImapTable' = [ImapTable EXCEPT ![d] = ImapTable[d] \ {inboxRecord}]
    /\ UNCHANGED <<ExpectedUid, SentMessages, ReceivedMessages>>

(* Device `d' on the server that does not support MOVE
   emulates the MOVE by doing COPY and scheduling the
   message for deletion.
 *)
CopyMessage(d, inboxRecord) ==
  \E r \in Storage["inbox"] :
    /\ r.uid = inboxRecord.uid
    /\ Storage' =
         [Storage EXCEPT !["movebox"] = Storage["movebox"] \union
                           {[uid |-> UidNext["movebox"],
                             messageId |-> r.messageId,
                             seen |-> r.seen]} ]
    /\ UidNext' = [UidNext EXCEPT !["movebox"] = UidNext["movebox"] + 1]
    /\ ImapTable' = [ImapTable EXCEPT ![d] = (ImapTable[d] \ {inboxRecord}) \union
         {[inboxRecord EXCEPT !.delete = TRUE]}]
    /\ UNCHANGED <<ExpectedUid, SentMessages, ReceivedMessages>>

(* Device `d' tries to move or copy the message that does not exist on the server
   and learns that the message does not exist,
   therefore removes the invalid record from its database.

   Copy failure is not modelled separately as it is indistinguishable
   from the move failure.
 *)
MoveMessageFailure(d, inboxRecord) ==
  /\ \A r \in Storage["inbox"] : r.uid /= inboxRecord.uid \* There is no such UID in the Inbox folder.
  /\ ImapTable' = [ImapTable EXCEPT ![d] = ImapTable[d] \ {inboxRecord}]
  /\ ServerUnchanged
  /\ UNCHANGED <<ExpectedUid, ReceivedMessages>>

(* Device d attempts to move a message from Inbox to Movebox. *)
\* FIXME: only move the message with the lowest UID to avoid reordering.
MoveMessage(d) ==
  \E inboxRecord \in ImapTable[d] :
    /\ inboxRecord.folder = "inbox" \* Device knows about a message in the Inbox.
    /\ inboxRecord.delete = FALSE \* This message is not scheduled for deletion.
    /\ \A r \in ImapTable[d] : \* Device does not know about any copy of this message in the Movebox.
       r.folder = "movebox" => r.messageId /= inboxRecord.messageId
    /\
      \/ MoveMessageSuccess(d, inboxRecord)
      \/ CopyMessage(d, inboxRecord)
      \/ MoveMessageFailure(d, inboxRecord)

(* Device `d' attempts to delete a message from the Inbox for which it believes a copy exists in the Movebox. *)
\* TODO: test instead that all such messages are scheduled for deletion at any time.
DeleteInboxMessage(d) ==
  \E inboxRecord \in ImapTable[d] :
  \E moveboxRecord \in ImapTable[d] :
    /\ inboxRecord.folder = "inbox"
    /\ moveboxRecord.folder = "movebox"
    /\ inboxRecord.messageId = moveboxRecord.messageId
    /\ Storage' =
         [Storage EXCEPT !["inbox"] = {r \in Storage["inbox"] : r.uid /= inboxRecord.uid }]
    /\ ImapTable' = [ImapTable EXCEPT ![d] = ImapTable[d] \ {inboxRecord}]
    /\ UNCHANGED <<UidNext, ExpectedUid, SentMessages, ReceivedMessages>>

(* Device `d' attempts to delete a message scheduled for deletion.

   Note that there is no check that the message deleted has the correct Message-ID,
   the device assumes that its knowledge of Message-ID to UID correspondence is correct
   and deletes by UID without checking.
   Regardless of whether the message is deleted on the server or there was no message with such UID,
   device deletes its record about this message.
   *)
DeleteMessage(d) ==
  \E record \in ImapTable[d] :
    /\ record.delete = TRUE
    /\ Storage' =
         [Storage EXCEPT ![record.folder] = {r \in Storage[record.folder] : r.uid /= record.uid}]
    /\ ImapTable' = [ImapTable EXCEPT ![d] = ImapTable[d] \ {record}]
    /\ UNCHANGED <<UidNext, ExpectedUid, SentMessages, ReceivedMessages>>

Next ==
  \/ \E m \in MessageIds : MessageArrives(m)
  \/ \E d \in Devices :
       \/ \E f \in Folders : FetchFolder(d, f)
       \/ PullFolder(d, "movebox") \* Pull only from Movebox to prevent reordering.
       \/ MoveMessage(d)
       \/ DeleteInboxMessage(d)
       \/ DeleteMessage(d)

----------------------------------------------------------------------------

(* An invariant stating that if some device has a record about some message on the IMAP server,
   this record has a correct Message-ID field.
   *)
ImapTableCorrect ==
  \A device \in Devices :
  \A record \in ImapTable[device] :
  \A stored \in Storage[record.folder] :
  record.uid = stored.uid => record.messageId = stored.messageId

(* The order of message reception is the same for every device.
   This is a weak "no reordering" property, the messages may still be reordered
   compared to the order of delivery to the Inbox, but they have to be
   reordered the same way for every device.

   This is achieved by only pulling from the Movebox.

   This property implies that devices are partially ordered by
   their received message sets.
 *)
NoReordering ==
  \A device1 \in Devices :
  \A device2 \in Devices :
  \/ ReceivedMessages[device1] \subseteq ReceivedMessages[device2]
  \/ ReceivedMessages[device2] \subseteq ReceivedMessages[device1]

Spec == Init /\ [][Next]_<<Storage,
                           UidNext,
                           ExpectedUid,
                           SentMessages,
                           ReceivedMessages,
                           ImapTable>>

THEOREM Spec => [](TypeOK /\
                   ImapTableCorrect /\
                   NoReordering)

=============================================================================
