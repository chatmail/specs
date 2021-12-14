----------------------------- MODULE deltachat -----------------------------

(*
There is a server and there are multiple devices of the same user.

The server has two folders: Inbox folder and Move folder.
Both folders have UID_NEXT property, which is the next UID assigned to the message dropped into this folder.
We don't model UIDVALIDITY.

To model both the case when the server support atomic MOVE operation
and the case when it doesn't, 
we will allow the devices to execute any of the two operations:
1. MOVE the message to the Move folder atomically.
2. COPY the message to the Move folder and schedule DELETE operation on the Inbox.

We want to check the following properties:
1. All the devices eventually become aware of all the messages arriving into the Inbox folder.
2. All the messages are eventually in the Move folder.
3. Eventually there are no messages in the Inbox folder.
4. Eventually device IMAP table represents the IMAP server state exactly.

IMAP table is a new solution proposed in https://github.com/deltachat/deltachat-core-rust/issues/1334

We assume that all devices want to move messages to the Movebox.
If no devices want to move messages to Movebox, things are simple, because devices only fetch the messages.
However, if some devices move the messages, while other devices don't,
the devices which have seen some message in the inbox and then seen them in the movebox
will never learn that the message was removed from the inbox.
This can also happen if some device deletes the message (does not matter whether it happens in the inbox or movebox)
while other devices never learn that it is deleted because they never attempt any actions against it.

TODO:
1. Model the case when the message may arrive multiple times.
   Maybe just don't delete the messages from the set of sent messages
   when they are delivered?
2. Model the seen state.
3. Model UIDVALIDITY reset at arbitrary times.
4. Model reception of message deletion and flags changes when device is offline?
   Deletion: https://github.com/deltachat/deltachat-core-rust/issues/1332
   Maybe not needed, because it can randomly fail when we are offline, so it cannot be relied on anyway.
*)

\* We need naturals for UIDs.
EXTENDS Naturals

CONSTANT Devices, \* Symmetry set of devices {d1, d2}
         MessageIds \* Symmetry set of Message-IDs {m1, m2, m3}

VARIABLES InboxFolder, \* The set of messages in the Inbox folder
          MoveFolder, \* The set of messages in the Move folder
          UidNext, \* UID that will be assigned to the next message in a folder.
          ExpectedUid, \* Function from folder to the next expected UID.
          SentMessages, \* The set of Message-IDs that have been sent and may eventually arrive into the inbox.
          ReceivedMessages,
          ImapTable \* Device view of the IMAP server state.

(* Set of all possible messages on the IMAP server *)     
Messages ==
  [uid : Nat, messageId : MessageIds, seen: BOOLEAN]

Folders ==
  {"inbox", "movebox"}

(* The set of possible records in the relational database on the device.
   Note that there may be multiple records for the same Message-ID
   if the message was seen both in the Inbox and Movebox.
*)
ImapRecords ==
  [messageId: MessageIds, uid: Nat, folder: Folders]

TypeOK ==
  /\ InboxFolder \subseteq [uid : Nat, messageId : MessageIds]
  /\ \A m1, m2 \in InboxFolder : m1 /= m2 => m1.uid /= m2.uid \* UIDs in the Inbox are unique.
  /\ MoveFolder \subseteq [uid : Nat, messageId: MessageIds] \* UIDs in the Movebox are unique.
  /\ \A m1, m2 \in MoveFolder : m1 /= m2 => m1.uid /= m2.uid
  /\ UidNext \in [Folders -> Nat]
  /\ ExpectedUid \in [Devices -> [Folders -> Nat]]
  /\ SentMessages \subseteq MessageIds
  /\ ReceivedMessages \in [Devices -> SUBSET [uid : Nat, messageId : MessageIds]]
  /\ ImapTable \in [Devices -> SUBSET ImapRecords]

(* Server has not been changed. Sent messages are not part of the server state,
   but we include the set of sent messages because the only way it can change
   is by the message being delivered to the server *)
ServerUnchanged ==
  UNCHANGED <<InboxFolder,
              MoveFolder,
              UidNext,
              SentMessages>>

\* A message with Message-Id m arrives into the Inbox folder.
MessageArrives(m) ==
  /\ m \in SentMessages \* This message has never arrived yet
  /\ InboxFolder' = InboxFolder \union {[uid |-> UidNext["inbox"], messageId |-> m]}
  /\ UidNext' = [UidNext EXCEPT !["inbox"] = UidNext["inbox"] + 1]
  /\ SentMessages' = { x \in SentMessages : x /= m }
  /\ UNCHANGED <<MoveFolder, ExpectedUid, ReceivedMessages, ImapTable>>
            
(*
Each device may FETCH from the folder at any time.
This includes the case when the device always fetches at the right time,
so we don't need to model the IDLE protocol.
We also don't model separate FETCH request and response.
Instead, FETCH operation makes the device aware of all the new messages since the last seen UID
and updates the last seen UID to the UID next.
The device gets no information about whether the messages it fetched previously are deleted.
*)

(* Device d fetches the messages from the f folder *)
FetchFolder(d, f) ==
  /\ \A d2 \in Devices : ExpectedUid[d][f] <= UidNext[f]
  /\ ExpectedUid' = [ExpectedUid EXCEPT ![d][f] = UidNext[f]]
  /\ UNCHANGED ReceivedMessages \* FIXME
  /\ ServerUnchanged
  /\ ImapTable' = [ImapTable EXCEPT ![d] = ImapTable[d] \union
       LET NewMessages == {x \in InboxFolder : x.uid >= ExpectedUid[d]["inbox"]}
       IN {[uid |-> r.uid,
            messageId |-> r.messageId,
            folder |-> "inbox"] : r \in NewMessages }]
            
(* Device `d` successfully moves the message with UID `uid` from the Inbox to the Movebox.
   Note that there is no check that the message being moved has the Message-ID that the device
   thinks is stored under this UID. If ImapTable is incorrect, it is possible
   to successfully move the wrong message.
 *)
MoveMessageSuccess(d, inboxRecord) ==
  \E r \in InboxFolder :
    /\ r.uid = inboxRecord.uid \* The message actually exists in the Inbox folder.
    /\ InboxFolder' = {x \in InboxFolder : x /= r} \* Remove the message from the Inbox folder.
    /\ MoveFolder' = MoveFolder \union {[uid |-> UidNext["movebox"], messageId |-> r.messageId]}
    /\ UidNext' = [UidNext EXCEPT !["movebox"] = UidNext["movebox"] + 1]
    /\ ImapTable' = [ImapTable EXCEPT ![d] = ImapTable[d] \ {inboxRecord}]
    /\ UNCHANGED <<ExpectedUid, ReceivedMessages, SentMessages>>

(* Device `d` tries to move the message that does not exists on the server
   and learns that the message does not exist,
   therefore removes the record. *)
MoveMessageFailure(d, inboxRecord) ==
  /\ \A r \in InboxFolder : r.uid /= inboxRecord.uid \* There is no such UID in the Inbox folder.
  /\ ImapTable' = [ImapTable EXCEPT ![d] = ImapTable[d] \ {inboxRecord}]
  /\ ServerUnchanged
  /\ UNCHANGED <<ExpectedUid, ReceivedMessages>>

(* Device d attempts to move a message from Inbox to Movebox *)
MoveMessage(d) ==
  \E inboxRecord \in {x \in ImapTable[d] : x.folder = "inbox"} :    \* Device knows about a message in the Inbox.
    \/ \A r \in ImapTable[d] : r.messageId /= inboxRecord.messageId \* Device does not know about any copy of this message in the Movebox.
    \/ MoveMessageSuccess(d, inboxRecord)
    \/ MoveMessageFailure(d, inboxRecord)

Init ==
  /\ InboxFolder = {}
  /\ MoveFolder = {}
  /\ UidNext = [f \in Folders |-> 0]
  /\ ExpectedUid = [d \in Devices |-> [f \in Folders |-> 0]]
  /\ SentMessages = MessageIds
  /\ ReceivedMessages = [d \in Devices |-> {}]
  /\ ImapTable = [d \in Devices |-> {}]

Next ==
  \/ \E m \in MessageIds : MessageArrives(m)
  \/ \E d \in Devices : \E f \in Folders : FetchFolder(d, f)
  \/ \E d \in Devices : MoveMessage(d)
  
(* An invariant stating that if some device has a record about some message on the IMAP server,
   this record has a correct Message-ID field.
   *)
ImapTableCorrect ==
  \A d \in Devices :
  \A r \in ImapTable[d] :
    TRUE

=============================================================================
