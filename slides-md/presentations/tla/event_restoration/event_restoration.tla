---- MODULE event_restoration ----
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANT NULL

(* --algorithm event_restoration
variables     
    HotStorage = {};
    ColdStorage = {Append("doc", ToString(x)): x \in {1,2,3}};
    EventRestorationQueue = <<>>;
    NotificationQueue = <<>>;
    Metadata \in [ColdStorage -> {[restoreBeginTime |-> NULL]}];
    CurrentTimeInSeconds = 0; \* models monotonic time

define
    SecondsDelta == 10 .. 500
    \* this will move time (CurrentTimeInSeconds) forward in ranges from 10 to 500 seconds.
    Tick(time) ==
        LET
            seconds == RandomElement(SecondsDelta)
        IN
            time + seconds
end define;

macro tick()
begin
    CurrentTimeInSeconds := Tick(CurrentTimeInSeconds)
end macro

macro dequeue(queue, receiver)
begin
  await queue /= <<>>;
  receiver := Head(queue);
  queue := Tail(queue);
end macro

macro enqueue(queue, message)
begin
    queue := Append(queue, message);
end macro

macro updateRestorationTime(doc)
begin
    Metadata[doc]["restoreBeginTime"] := CurrentTimeInSeconds;
end macro

process producer = "producer"
variables
    notificationFromQueue = NULL;
    doc \in ColdStorage;
begin
    AskForRestoration:
        tick();
        enqueue(EventRestorationQueue, doc);
    
    WaitForNotification:
        tick();
        dequeue(NotificationQueue, notificationFromQueue);
    
        assert notificationFromQueue \notin ColdStorage;
        assert notificationFromQueue \in HotStorage;
end process;

process consumer = "consumer"
variables
    docFromQueue = NULL;
begin
    TryRestoring:
        tick();
        dequeue(EventRestorationQueue, docFromQueue);
        updateRestorationTime(docFromQueue);
    
        HotStorage := HotStorage \union {docFromQueue};
        ColdStorage := ColdStorage \ {docFromQueue};

        enqueue(NotificationQueue, docFromQueue);

end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "8462aef" /\ chksum(tla) = "3a869432")
VARIABLES HotStorage, ColdStorage, EventRestorationQueue, NotificationQueue, 
          Metadata, CurrentTimeInSeconds, pc

(* define statement *)
SecondsDelta == 10 .. 500

Tick(time) ==
    LET
        seconds == RandomElement(SecondsDelta)
    IN
        time + seconds

VARIABLES notificationFromQueue, doc, docFromQueue

vars == << HotStorage, ColdStorage, EventRestorationQueue, NotificationQueue, 
           Metadata, CurrentTimeInSeconds, pc, notificationFromQueue, doc, 
           docFromQueue >>

ProcSet == {"producer"} \cup {"consumer"}

Init == (* Global variables *)
        /\ HotStorage = {}
        /\ ColdStorage = {Append("doc", ToString(x)): x \in {1,2,3}}
        /\ EventRestorationQueue = <<>>
        /\ NotificationQueue = <<>>
        /\ Metadata \in [ColdStorage -> {[restoreBeginTime |-> NULL]}]
        /\ CurrentTimeInSeconds = 0
        (* Process producer *)
        /\ notificationFromQueue = NULL
        /\ doc \in ColdStorage
        (* Process consumer *)
        /\ docFromQueue = NULL
        /\ pc = [self \in ProcSet |-> CASE self = "producer" -> "AskForRestoration"
                                        [] self = "consumer" -> "TryRestoring"]

AskForRestoration == /\ pc["producer"] = "AskForRestoration"
                     /\ CurrentTimeInSeconds' = Tick(CurrentTimeInSeconds)
                     /\ EventRestorationQueue' = Append(EventRestorationQueue, doc)
                     /\ pc' = [pc EXCEPT !["producer"] = "WaitForNotification"]
                     /\ UNCHANGED << HotStorage, ColdStorage, 
                                     NotificationQueue, Metadata, 
                                     notificationFromQueue, doc, docFromQueue >>

WaitForNotification == /\ pc["producer"] = "WaitForNotification"
                       /\ CurrentTimeInSeconds' = Tick(CurrentTimeInSeconds)
                       /\ NotificationQueue /= <<>>
                       /\ notificationFromQueue' = Head(NotificationQueue)
                       /\ NotificationQueue' = Tail(NotificationQueue)
                       /\ Assert(notificationFromQueue' \notin ColdStorage, 
                                 "Failure of assertion at line 60, column 9.")
                       /\ Assert(notificationFromQueue' \in HotStorage, 
                                 "Failure of assertion at line 61, column 9.")
                       /\ pc' = [pc EXCEPT !["producer"] = "Done"]
                       /\ UNCHANGED << HotStorage, ColdStorage, 
                                       EventRestorationQueue, Metadata, doc, 
                                       docFromQueue >>

producer == AskForRestoration \/ WaitForNotification

TryRestoring == /\ pc["consumer"] = "TryRestoring"
                /\ CurrentTimeInSeconds' = Tick(CurrentTimeInSeconds)
                /\ EventRestorationQueue /= <<>>
                /\ docFromQueue' = Head(EventRestorationQueue)
                /\ EventRestorationQueue' = Tail(EventRestorationQueue)
                /\ Metadata' = [Metadata EXCEPT ![docFromQueue']["restoreBeginTime"] = CurrentTimeInSeconds']
                /\ HotStorage' = (HotStorage \union {docFromQueue'})
                /\ ColdStorage' = ColdStorage \ {docFromQueue'}
                /\ NotificationQueue' = Append(NotificationQueue, docFromQueue')
                /\ pc' = [pc EXCEPT !["consumer"] = "Done"]
                /\ UNCHANGED << notificationFromQueue, doc >>

consumer == TryRestoring

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == producer \/ consumer
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
