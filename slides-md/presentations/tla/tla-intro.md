---
title:  TLA+
subtitle: And how to use it to catch bugs
author: Pepe García <pepe@goodnotes.com>
email: pepe@goodnotes.com
---

# Plan for today

- Why model systems?
- What is TLA+?
- How to use TLA+?
- Use in the real world

# Glossary

- **System**: the thing we're trying to model.
- **Model**: a description of a system.
- **State space**: the set of all possible states of a system.
- **State**: the snapshot of the system at a given point in time.
- **Behaviour**: a _path_ in the state graph

# Why model systems?

:::{.columns}
::::{.column}
We model systems to undertand them better, and to be able to proof certain properties of them.
::::
::::{.column}
![](https://ds1.static.rtbf.be/article/image/1240x800/a/d/1/97427b4a894f63258b38151d8f0752e4-1507811971.jpg)
::::
:::

# Why model systems?

Remember, the map is not the territory.  We're trying to understand the
territory, not the map.

When modelling our system and proving properties of it, we're proving properties
of the model, which should map to our system correctly.

# Why model systems?

\begin{alertblock}{Warning}
With TLA+, we're gonna write code to model our system, but we won't be able to use this code to generate code for our system.
\end{alertblock}

# Why model systems?

![](./slides-md/presentations/tla/amazon_excerpt.png){width=400px}

From Lamport's comment on Amazon's paper[^1].

# What is TLA+?

- TLA+ is a formal specification language
- invented by Leslie Lamport (Turing award 2013, Paxos, Lamport Clocks, ...)
- used to model concurrent systems

```tla+
VARIABLE clock

Init == clock \in {0, 1}

Tick == IF clock = 0 THEN clock' = 1 ELSE clock' = 0

Spec == Init /\ [][Tick]_<<clock>>
```

# What's PlusCal?

- PlusCal is a high-level language that compiles to TLA+
- It's easier to write, and closer to imperative languages

```tla+
-- fair algorithm OneBitClock {
  variable clock \in {0, 1};
  {
    while (TRUE) {
      if (clock = 0)
        clock := 1
      else 
        clock := 0    
    }
  }
}
```

. . .

**We can think of TLA+ as the assembly specification language and PlusCal as C, that compiles to it**

# Use in the real world

- AWS[^2]
- Microsoft[^3]
- Oracle[^4]
- ...
- GoodNotes

# Quick intro to PlusCal

- `while`, `if`... have the same semantics as in any other language
- Lists are delimited by `<<` and `>>` and comma separated.
- Sets are enclosed by `{` and `}`, and comma separated.
- Dictionaries are enclosed by `[` and `]`, and are comma separated.  Keys and values are mapped via `|->`.
- Functions are functions in the mathematical way, mapping between a domain set and a codomain set.  The closest to functions in  other languages are operators.
- We create processes to denote independent processes in our system.

# Quick intro to PlusCal

Let's demo it!

Let's create a model for a simple system: A wire transfer with overdraft protection.

Open **`overdraft.tla`**.

# Quick intro to Pluscal

Remember that PlusCal transpiles to TLA+, we need to first convert it to TLA+.

And then, run TLC in the compiled model.

# Real world example

At work, we try to save money by moving events from our event storage from a
_hot_ storage to a _cold_ storage.  This is, from a relational DB, to S3.

Sometimes, the number of events for a single document is huge, and restoring it
takes a long time.  Initially, our algorithm for restoring a _cold_ stream of
document events was something like this in pseudocode:

```python
def restore_events(event_stream_id):
    restored = False
    while not restored:
        try:
            enqueue_restoration_request(event_stream_id)
            # timeout in 60 secs
            wait_for_notification(event_stream_id, 60)
            restored = True
        catch TimeoutException:
            continue
```

# Real world example

Of course, we have a consumer counterpart:

```python
class RestorationRequestConsumer:
    def consume(event):
        restore_events_to_hot_storage(event.stream_id)

        notify_restoration_done(event.stream_id)
```

# Real world example

You can see that we have a producer, and a consumer.  The producer will wait for
a minute for a notification that the consumer finished working.  If it doesn't
get the notification, it will enqueue again.

The way we were autoscaling this particular piece didn't have the _queue
pressure_ into consideration to add more consumers, and we wound up having an
incident in this subsystem, because the producer was publishing more and more
events even though the consumer wasn't able to keep up.

The problematic part for us was to just wait for a minute and then retry.


# Real world example. Solution

:::{.columns}
::::{.column}
Let's write this in Pluscal and see if we can model it to find the error.
::::
::::{.column}
![](https://lamport.azurewebsites.net/tla/splash_small.png)
::::
:::

# Real world example. Solution

Head to **`0_event_restoration.tla`**.

# Real world example. Solution

After running it, you can see that we're encountering an error.  Our invariant
is violated, meaning that we're enqueuing the same event twice.

This is great, we've managed to reproduce the error in our model, but we gotta
find a solution now.

# Real world example. Solution

Now, on the consumer side, we will update the restoration time when we start working on an event.

```python
class RestorationRequestConsumer:
    def consume(event):
        update_restore_time(event, now())
        restore_events_to_hot_storage(event.stream_id)

        notify_restoration_done(event.stream_id)
```

# Real world example. Solution

And, we'll update the producer to check if the restoration time is too old, and
only then start working on it.

```python
def restore_events(event_stream_id):
    restored = False
    while not restored:
        try:
            enqueue_restoration_request(event_stream_id)
            # timeout in 60 secs
            wait_for_notification(event_stream_id, 60)
            restored = True
        catch TimeoutException:
            if is_restoration_too_old(event_stream_id):
                continue
            else:
                wait(60)
                continue
```

# Real world example. Solution

Head over to **`1_fixing_invariant.tla`**.

# Thanks

Thank to my **amazing colleages** that didn't need formal verification to
understand this, and helped me with actual examples of how the previous model
could fail, and be fixed,


[^1]: <https://lamport.azurewebsites.net/tla/amazon-excerpt.html>
[^2]: <https://awsmaniac.com/how-formal-methods-helped-aws-to-design-amazing-services/>
[^3]: <https://www.microsoft.com/en-us/research/blog/tla-foundation-aims-to-bring-math-based-software-modeling-to-the-mainstream/>
[^4]: <https://blogs.oracle.com/cloud-infrastructure/post/sleeping-soundly-with-the-help-of-tla>
