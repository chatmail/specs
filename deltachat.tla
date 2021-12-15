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
   uid: Nat, \* Special value of 0 indicates that UID is unknown.
   folder: Folders]

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
     (r1.folder = r2.folder /\
      r1.uid > 0 /\               \* Only for real UIDs.
      r1.uid = r2.uid) => r1 = r2

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

(* Device d fetches the messages from the f folder. *)
FetchFolder(d, f) ==
  LET
    NewMessages == {x \in Storage[f] : x.uid >= ExpectedUid[d][f]}
    OldDummyRecords ==
      { r \in ImapTable[d] :
        /\ r.folder = f
        /\ \E x \in NewMessages : r.messageId = x.messageId
        /\ r.uid = 0 }
  IN
  /\ ExpectedUid' = [ExpectedUid EXCEPT ![d][f] = UidNext[f]]
  /\ UNCHANGED ReceivedMessages
  /\ ServerUnchanged
  /\ ImapTable' = [ImapTable EXCEPT ![d] =
        (ImapTable[d] \ OldDummyRecords)
        \union {[uid |-> r.uid,
                 messageId |-> r.messageId,
                 folder |-> f] : r \in NewMessages }]
                 
(* Fetch message contents. *)
PullFolder(d, f) ==
  LET
    RequestedRecords ==
      {r \in ImapTable[d] : /\ r.uid > 0
                            /\ r.folder = f
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
   
   Device does not know the UID of the moved message, but creates a dummy record
   anyway to avoid moving another copy of the message from the Inbox if it exists for some reason.
   
   After moving, UIDs are assumed to be unknown.
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
    /\ LET NewRecord == [uid |-> 0, \* Unknown UID.
                         messageId |-> inboxRecord.messageId,
                         folder |-> "movebox"]
       IN
         ImapTable' =
           [ImapTable EXCEPT ![d] = (ImapTable[d] \union {NewRecord}) \ {inboxRecord}]
    /\ UNCHANGED <<ExpectedUid, SentMessages, ReceivedMessages>>

(* Device `d' successfully copies the message from the Inbox to Movebox.
 This happens when the server does not support atomic MOVE,
 so the device has to resort to copying the message and then deleting remaining copy from the Inbox.
 
It is especially important to create a dummy record here to make sure we don't keep
copying this message until we fetch from the Movebox and learn about the copy.
 *)
CopyMessageSuccess(d, inboxRecord) ==
  \E r \in Storage["inbox"] :
    /\ r.uid = inboxRecord.uid
    /\ Storage' =
         [Storage EXCEPT !["movebox"] = Storage["movebox"] \union
                           {[uid |-> UidNext["movebox"],
                             messageId |-> r.messageId,
                             seen |-> r.seen]}]
    /\ UidNext' = [UidNext EXCEPT !["movebox"] = UidNext["movebox"] + 1]
    /\ ImapTable' = [ImapTable EXCEPT ![d] =
                       ImapTable[d] \union {[uid |-> 0, \* Unknown UID.
                                             messageId |-> inboxRecord.messageId,
                                             folder |-> "movebox"]}]
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
    /\ inboxRecord.uid > 0 \* This is not a dummy record (although there should never be one for the Inbox).
    /\ \A r \in ImapTable[d] : \* Device does not know about any copy of this message in the Movebox.
       r.folder = "movebox" => r.messageId /= inboxRecord.messageId
    /\ 
      \/ MoveMessageSuccess(d, inboxRecord)
      \/ CopyMessageSuccess(d, inboxRecord)
      \/ MoveMessageFailure(d, inboxRecord)

(* Device `d' attempts to delete a message from the Inbox for which it believes a copy exists in the Movebox.
   Note that there is no check that the message deleted has the correct Message-ID,
   the device assumes that its knowledge of Message-ID to UID correspondence is correct
   and deletes by UID without checking.
   Regardless of whether the message is deleted on the server or there was no message with such UID,
   device deletes its record about this message.
 *)
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

Next ==
  \/ \E m \in MessageIds : MessageArrives(m)
  \/ \E d \in Devices :
       \/ \E f \in Folders : FetchFolder(d, f)
       \/ PullFolder(d, "movebox") \* Pull only from Movebox to prevent reordering.
       \/ MoveMessage(d)
       \/ DeleteInboxMessage(d)
  
----------------------------------------------------------------------------

(* An invariant stating that if some device has a record about some message on the IMAP server,
   this record has a correct Message-ID field.
   *)
ImapTableCorrect ==
  \A device \in Devices :
  \A record \in ImapTable[device] :
  \A stored \in Storage[record.folder] :
  record.uid = stored.uid => record.messageId = stored.messageId

(* An invariant stating that it is impossible to have both a dummy (UID 0)
   and non-dummy record for the same message in the same folder. *)
ImapTableNoDummyRecords ==
  \A device \in Devices :
  \A messageId \in MessageIds :
  \A folder \in Folders :
    \/ \A r \in ImapTable[device] : \* All records are real.
         (r.folder = folder /\ r.messageId = messageId) => r.uid > 0
    \/ \A r \in ImapTable[device] : \* All records are dummy.
         (r.folder = folder /\ r.messageId = messageId) => r.uid = 0
 
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
                   ImapTableNoDummyRecords /\
                   NoReordering)

=============================================================================
