---- MODULE 1_fixing_invariant ----
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANT NULL

(* --algorithm 1_fixing_invariant
variables     
    HotStorage = {};
    ColdStorage = {Append("doc", ToString(x)): x \in {1}};
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
    ToSet(s) == { s[i] : i \in DOMAIN s }
    TheresNoRepeatedMessages == Len(EventRestorationQueue) = Cardinality(ToSet(EventRestorationQueue))
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
    condition = FALSE;
begin
    AskForRestoration:
        tick();
        enqueue(EventRestorationQueue, doc);

    AskForRestorationAgain:
        tick();
        condition :=
                /\ Metadata[doc]["restoreBeginTime"] /= NULL
                /\ CurrentTimeInSeconds - Metadata[doc]["restoreBeginTime"] < 60
                /\ EventRestorationQueue # <<>>
                /\ doc \in ColdStorage;

        if condition then
            enqueue(EventRestorationQueue, doc);
        end if;    
    
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
        if docFromQueue \notin HotStorage then
            updateRestorationTime(docFromQueue);
        
            HotStorage := HotStorage \union {docFromQueue};
            ColdStorage := ColdStorage \ {docFromQueue};

            enqueue(NotificationQueue, docFromQueue);
        end if;

end process;
end algorithm; *)
====
