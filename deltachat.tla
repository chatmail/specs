----------------------------- MODULE deltachat -----------------------------

(***************************************************************************)
(* Model of a single IMAP server and multiple devices.                     *)
(*                                                                         *)
(* Devices fetch the messages and move them from the Inbox folder to       *)
(* the Movebox folder on the server.                                       *)
(***************************************************************************)

EXTENDS Naturals, (* We need naturals for `^UIDs.^' *)
        Sequences (* Sequences of Message-IDs scheduled for delivery. *)

CONSTANT Devices, (* Symmetry set of devices such as `{d1, d2}'. *)
         MessageIds, (* Symmetry set of Message-IDs such as `{m1, m2}'. *)
         InitSentMessages (*************************************************)
                          (* Sequence of Message-IDs in the order of       *)
                          (* delivery, such as <<m1, m1, m2, m1>>          *)
                          (*************************************************)

VARIABLES Storage, \* The set of messages in the server folders.
          UidNext, \* `^UID^' that will be assigned to the next message in a folder.
          LastSeenUid, \* Function from folder to the next expected `^UID.^'
          SentMessages,(****************************************************)
                       (* The set of Message-IDs that have been sent and   *)
                       (* may eventually arrive into the Inbox.            *)
                       (****************************************************)
          ReceivedMessages, \* Sequences of Message-IDs downloaded by the devices.
          ImapTable \* Device view of the IMAP server state.

vars == <<Storage, UidNext, LastSeenUid, SentMessages, ReceivedMessages, ImapTable>>

(* The server has two folders: Inbox and Movebox. *)
Folders ==
  {"inbox", "movebox"}

(* The set of possible records on the server. *)
StorageRecords ==
  [uid : Nat \ {0}, messageId : MessageIds]

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
  /\ LastSeenUid \in [Devices -> [Folders -> Nat]]
  /\ SentMessages \in Seq(MessageIds)
  /\ ReceivedMessages \in [Devices -> Seq(MessageIds)]
  /\ ImapTable \in [Devices -> SUBSET ImapRecords]
  /\ \A d \in Devices :
     \A r1, r2 \in ImapTable[d] : \* Uniqueness constraint.
     (r1.folder = r2.folder /\ r1.uid = r2.uid) => r1 = r2

Init ==
  /\ Storage = [f \in Folders |-> {}]
  /\ UidNext = [f \in Folders |-> 1]
  /\ LastSeenUid = [d \in Devices |-> [f \in Folders |-> 0]]
  /\ SentMessages = InitSentMessages
  /\ ReceivedMessages = [d \in Devices |-> <<>>]
  /\ ImapTable = [d \in Devices |-> {}]

----------------------------------------------------------------------------

(***************************************************************************)
(* Server has not been changed.  Sent messages are not part of the server  *)
(* state, but we include the set of sent messages because the only way it  *)
(* can change is by the message being delivered to the server              *)
(***************************************************************************)
ServerUnchanged ==
  UNCHANGED <<Storage,
              UidNext,
              SentMessages>>

----------------------------------------------------------------------------

(* A message with Message-ID `m' arrives into the Inbox folder. *)
MessageArrives(m) ==
  /\ SentMessages /= <<>>
  /\ Storage' = [Storage EXCEPT !["inbox"] = Storage["inbox"] \union
                                {[uid |-> UidNext["inbox"],
                                  messageId |-> Head(SentMessages)]}]
  /\ UidNext' = [UidNext EXCEPT !["inbox"] = UidNext["inbox"] + 1]
  /\ SentMessages' = Tail(SentMessages)
  /\ UNCHANGED <<LastSeenUid, ReceivedMessages, ImapTable>>

----------------------------------------------------------------------------

(***************************************************************************)
(* Devices fetch, move and delete messages.  These actions can be batched, *)
(* but we consider all possible orders of them and consider an action on a *)
(* single message at any time.                                             *)
(***************************************************************************)

(***************************************************************************)
(* Each device may FETCH from the folder at any time.  This includes       *)
(* the case when the device always fetches at the right time, so we don't  *)
(* need to model the IDLE protocol.  We also don't model separate FETCH    *)
(* request and response.  Instead, FETCH operation makes the device aware  *)
(* of all the new messages since the last seen UID and updates the last    *)
(* seen UID to the UID next.  The device gets no information about whether *)
(* the messages it fetched previously are deleted.                         *)
(***************************************************************************)

(* Device d fetches the messages from the f folder.
   Duplicate messages are marked for deletion.
 *)
FetchFolder(d, f) ==
  \E storageRecord \in Storage[f] :
  /\ storageRecord.uid > LastSeenUid[d][f]
  /\ \A x \in Storage[f] :
       \/ x.uid <= LastSeenUid[d][f]
       \/ x.uid >= storageRecord.uid \* Fetch low UIDs first.
  /\ LastSeenUid' = [LastSeenUid EXCEPT ![d][f] = storageRecord.uid]
  /\ LET
       Duplicate == \* Can happen if message is copied to Movebox twice.
         \E x \in ImapTable[d] : /\ \/ (x.folder = f /\ x.uid < storageRecord.uid)
                                    \/ x.folder = "movebox"
                                 /\ x.messageId = storageRecord.messageId
                                 /\ x.delete = FALSE
       NewRecord ==
         [uid |-> storageRecord.uid,
          messageId |-> storageRecord.messageId,
          folder |-> f,
          delete |-> Duplicate]
       UpdatedRecordsBefore ==
         {x \in ImapTable[d] : /\ x.folder = "inbox"
                               /\ f = "movebox"
                               /\ x.messageId = storageRecord.messageId}
       UpdatedRecordsAfter ==
         {[x EXCEPT !.delete = TRUE] : x \in UpdatedRecordsBefore}
       NewImapTable == (****************************************************)
                       (* Remove first, then add.  Otherwise new/updated   *)
                       (* records may be deleted if they existed before.   *)
                       (****************************************************)
         (ImapTable[d] \ UpdatedRecordsBefore)
             \union UpdatedRecordsAfter
             \union {NewRecord}
     IN ImapTable' = [ImapTable EXCEPT ![d] = NewImapTable]
   /\ UNCHANGED <<Storage, UidNext, SentMessages, ReceivedMessages>>

DownloadMessageSuccess(d, imapRecord) ==
  \E storageRecord \in Storage[imapRecord.folder] :
  /\ storageRecord.uid = imapRecord.uid
  /\ ReceivedMessages' =
       [ReceivedMessages EXCEPT ![d] =
        Append(ReceivedMessages[d], storageRecord.messageId)]
  /\ ServerUnchanged
  /\ UNCHANGED <<LastSeenUid, ImapTable>>

(* Device d fails to download the message, because
   it does not exist on the server, and deletes corresponding local record.

   This should never happen. *)
DownloadMessageFailure(d, imapRecord) ==
  /\ \A storageRecord \in Storage[imapRecord.folder] :
          storageRecord.uid /= imapRecord.uid
  /\ ImapTable[d] = [ImapTable EXCEPT ![d] = ImapTable[d] \ {imapRecord}]
  /\ ServerUnchanged
  /\ UNCHANGED <<LastSeenUid, ImapTable>>

ShouldDownload(d, imapRecord) ==
  /\ imapRecord.folder = "movebox" \* Only download from the movebox to avoid reordering.
  /\ ~imapRecord.delete
  /\ \A i \in 1..Len(ReceivedMessages[d]) : imapRecord.messageId /= ReceivedMessages[d][i]

DownloadMessage(d) ==
  \E imapRecord \in ImapTable[d] :
  /\ ShouldDownload(d, imapRecord)
  /\ \A imapRecord2 \in ImapTable[d] : \* Download only the message with the lowest UID.
       (imapRecord.folder = imapRecord2.folder /\ ShouldDownload(d, imapRecord2))
         => imapRecord2.uid >= imapRecord.uid
  /\ \/ DownloadMessageSuccess(d, imapRecord)
     \/ DownloadMessageFailure(d, imapRecord)

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
                             messageId |-> r.messageId]}]
    /\ UidNext' = [UidNext EXCEPT !["movebox"] = UidNext["movebox"] + 1]
    /\ ImapTable' = [ImapTable EXCEPT ![d] = ImapTable[d] \ {inboxRecord}]
    /\ UNCHANGED <<LastSeenUid, SentMessages, ReceivedMessages>>

(***************************************************************************)
(* Device `d' on the server that does not support MOVE                     *)
(* emulates the MOVE by doing COPY and scheduling the message for          *)
(* deletion.                                                               *)
(***************************************************************************)
CopyMessage(d, inboxRecord) ==
  \E r \in Storage["inbox"] :
    /\ r.uid = inboxRecord.uid
    /\ Storage' =
         [Storage EXCEPT !["movebox"] = Storage["movebox"] \union
                           {[uid |-> UidNext["movebox"],
                             messageId |-> r.messageId]} ]
    /\ UidNext' = [UidNext EXCEPT !["movebox"] = UidNext["movebox"] + 1]
    /\ ImapTable' = [ImapTable EXCEPT ![d] = (ImapTable[d] \ {inboxRecord}) \union
         {[inboxRecord EXCEPT !.delete = TRUE]}]
    /\ UNCHANGED <<LastSeenUid, SentMessages, ReceivedMessages>>

(***************************************************************************)
(* Device `d' tries to move or copy the message that does not exist on the *)
(* server and learns that the message does not exist, therefore removes    *)
(* the invalid record from its database.                                   *)
(*                                                                         *)
(* Copy failure is not modelled separately as it is indistinguishable from *)
(* the move failure.                                                       *)
(***************************************************************************)
MoveMessageFailure(d, inboxRecord) ==
  /\ \A r \in Storage["inbox"] : r.uid /= inboxRecord.uid \* There is no such UID in the Inbox folder.
  /\ ImapTable' = [ImapTable EXCEPT ![d] = ImapTable[d] \ {inboxRecord}]
  /\ ServerUnchanged
  /\ UNCHANGED <<LastSeenUid, ReceivedMessages>>

ShouldMove(d, imapRecord) ==
  /\ imapRecord.folder = "inbox" \* Device knows about a message in the Inbox.
  /\ imapRecord.delete = FALSE \* This message is not scheduled for deletion.

(* Device d attempts to move a message from Inbox to Movebox. *)
\* FIXME: only move the message with the lowest UID to avoid reordering.
MoveMessage(d) ==
  \E imapRecord \in ImapTable[d] :
    /\ ShouldMove(d, imapRecord)
    /\ \A imapRecord2 \in ImapTable[d] :
         (imapRecord.folder = imapRecord2.folder /\ ShouldMove(d, imapRecord2))
           => imapRecord2.uid >= imapRecord.uid
    /\
      \/ MoveMessageSuccess(d, imapRecord)
      \/ CopyMessage(d, imapRecord)
      \/ MoveMessageFailure(d, imapRecord)

(* Device `d' attempts to delete a message from the Inbox for which it
   believes a copy exists in the Movebox. *)
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
    /\ UNCHANGED <<UidNext, LastSeenUid, SentMessages, ReceivedMessages>>

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
    /\ UNCHANGED <<UidNext, LastSeenUid, SentMessages, ReceivedMessages>>

Next ==
  \/ \E m \in MessageIds : MessageArrives(m)
  \/ \E d \in Devices :
       \/ \E f \in Folders : FetchFolder(d, f)
       \/ MoveMessage(d)
       \/ DeleteInboxMessage(d)
       \/ DeleteMessage(d)
       \/ DownloadMessage(d)

----------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK

(* An invariant stating that if some device has a record about some message on the IMAP server,
   this record has a correct Message-ID field.
   *)
ImapTableCorrect ==
  \A device \in Devices :
  \A record \in ImapTable[device] :
  \A stored \in Storage[record.folder] :
  record.uid = stored.uid => record.messageId = stored.messageId

THEOREM Spec => []ImapTableCorrect

(* The order of message reception is the same for every device.
   This is a weak "no reordering" property, the messages may still be reordered
   compared to the order of delivery to the Inbox, but they have to be
   reordered the same way for every device.

   This is achieved by only pulling from the Movebox.

   This property implies that devices are partially ordered by
   their received message sets.
 *)
WeakNoReordering ==
  \A device1 \in Devices :
  \A device2 \in Devices :
  LET
    s1 == ReceivedMessages[device1]
    s2 == ReceivedMessages[device2]
    l1 == Len(s1)
    l2 == Len(s2)
  IN
    (l1 <= l2) => (s1 = SubSeq(s2, 1, l1))

THEOREM Spec => []WeakNoReordering

Unique(s) ==
  IF s = <<>>
    THEN <<>>
    ELSE LET
           h == Head(s)
           Test(x) == x /= h
         IN
            <<h>> \o SelectSeq(Tail(s), Test)

CorrectReceptionOrder ==
  Unique(InitSentMessages)

StrongNoReordering ==
  \A device \in Devices :
  ReceivedMessages[device] =
  SubSeq(CorrectReceptionOrder, 1, Len(ReceivedMessages[device]))

THEOREM Spec => []StrongNoReordering

(* If there is a record for message in the Movebox,
   then it should be scheduled for deletion in the Inbox.

   This guarantees that we never move the message to the Movebox
   if we know that there is a copy already,
   because we don't move messages scheduled for deletion. *)
InboxMessagesScheduledForDeletionInvariant ==
  \A device \in Devices :
  \A inboxRecord \in ImapTable[device] :
  \A moveboxRecord \in ImapTable[device] :
  (/\ inboxRecord.folder = "inbox"
   /\ moveboxRecord.folder = "movebox"
   /\ moveboxRecord.messageId = inboxRecord.messageId)
  => inboxRecord.delete

THEOREM Spec => []InboxMessagesScheduledForDeletionInvariant

----------------------------------------------------------------------------

AllMessagesDownloaded ==
  \A i \in 1..Len(InitSentMessages) :
  \A d \in Devices :
  \E j \in 1..Len(ReceivedMessages[d]) :
  ReceivedMessages[d][j] = InitSentMessages[i]

(* All messages are downloaded eventually.
We also check that all messages are eventually always downloaded,
which means they are never undownloaded once they all are downloaded. *)
AllMessagesDownloadedEventually ==
  WF_vars(Next) => <>[]AllMessagesDownloaded

THEOREM Spec => AllMessagesDownloadedEventually

EmptyInboxEventually ==
  WF_vars(Next) => <>[](Storage["inbox"] = {})

THEOREM Spec => EmptyInboxEventually

(***************************************************************************)
(* Unlike ImapTableCorrect property, this is only satisfied eventually.    *)
(***************************************************************************)
ImapTableReflectsStorage ==
  \A d \in Devices :
  \A r \in ImapTable[d] :
  \E x \in Storage[r.folder] :
  /\ r.uid = x.uid
  /\ r.messageId = x.messageId
  /\ r.delete = FALSE

StorageReflectsImapTable ==
  \A d \in Devices :
  \A f \in Folders :
  \A x \in Storage[f] :
  \E r \in ImapTable[d] :
  /\ r.uid = x.uid
  /\ r.messageId = x.messageId
  /\ r.folder = f
  /\ r.delete = FALSE

PerfectImapTable ==
  ImapTableReflectsStorage /\ StorageReflectsImapTable

PerfectImapTableEventually ==
  WF_vars(Next) => <>[]PerfectImapTable

THEOREM Spec => PerfectImapTableEventually

=============================================================================
