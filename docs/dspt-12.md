---
title: Data Structures and Programmatic Thinking. Session 12
author: Pepe García
email: jgarciah@faculty.ie.edu
date: 2020-04-20
lang: en
---

Data Structures and Programmatic Thinking. Session 12
=====================================================

https://slides.com/pepegar/dspt-12/live

Plan for today
==============

-   Learn what\'s JSON
-   See how it relates to Python data structures

JSON
====

*Javascript Object Notation*


What is JSON
============

JSON is one of the most used data interchange format nowadays. It
provides a syntax **easy to understand for humans** and **easy to parse
for computers**.

JSON
====

``` {.json}
{
  "numbers": 1234,
  "strings": "this is a string",
  "booleans": true,
  "lists": [1, "string"],
  "nulls": null,
  "dictionaries": {
    "key": "value"
  }
}
```

Numbers
=======

``` {.json}
1234
```

Numbers in JSON, like in Python, are declared by just writing their
numeric representations

Strings
=======

``` {.json}
"hello world!"
```

Strings should be declared within double quotes.  It\'s not valid to use
single quotes.

Booleans
========

``` {.json}
false
```

For declaring booleans, we use the lowercased words **true** and
**false**

Null
====

``` {.json}
null
```

Null declares an empty value, as Python **None**

Lists
=====

``` {.json}
[1, true, "potato"]
```

Lists are declared within **square brackets** and with elements
separated by commas.  (they\'re called **arrays** in JSON)

Dictionaries
============

``` {.json}
{
  "first key": 3,
  "second key": false
}
```

Dictionaries (called **objects** in  JSON) are declared like in Python. 
The difference is that **keys must be strings** in JSON objects

Exercises
=========

```python
For these exercises we will use lobste.rs data from
the above URL.

1. Download the data to a file called lobsters.json
   and read it from Python

2. Create a function for *printing* all the titles.

3. Create a function that returns the number of
   articles per user.
```

https://lobste.rs/hottest.json
