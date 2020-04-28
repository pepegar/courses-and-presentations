---
title: Data Structures & Programmatic Thinking
author: Pepe García
email: jgarciah@faculty.ie.edu
date: 2020-04-20
lang: en
---

Data Structures & Programmatic Thinking
=======================================


Plan for this session
=====================

-   Learn about dictionaries

Dictionaries
============

Dictionaries are another kind of collection in Python.  Dictionaries\
  map keys to values.

 


Creating dictionaries
=====================

We use curly brackets (**{}**) to declare dictionaries.

```python
translations = {
    "es": "Hola!",
    "it": "Ciao!",
    "en": "Hello!"
}
```

colon for separating key and value

comma for separating entries

Creating dictionaries
=====================

We can also create empty dictionaries

```python
translations = {}
```

Creating dictionaries
=====================

Adding elements
===============

We add elements to dictionaries given their specific index:

```python
translations = {}
translations["en"] = "Hello"
translations["it"] = "Ciao"
translations["es"] = "Hola"
```

Adding elements
===============

Updating elements
=================

we always can change a value in the dictionary by re-assigning the key

```python
translations = {}
translations["en"] = "Hello"
translations["en"] = "WHATUP!"
```

Updating elements
=================

Deleting elements
=================

We can delete an element of the dictionary using the **pop** method

```python
translations = {}
translations["en"] = "Hello"
translations.pop("en")
```

Deleting elements
=================

Getting all keys or values
==========================

We can allways get all **keys** or **values** from the dict as a list
using either the **.keys()** or **.values()** method

```python
users = {
  1: "Pepe",
  22: "Peter",
  44143: "Johnny",
  2: "Chuck"
}

users.keys()
users.values()
```

Getting all keys or values
==========================

for loops
=========

In the same way we used **for** loops to iterate over elements of a
list, we can use them to iterate over elements of a dictionary.

 

The difference is that, with dictionaries, the **iteration variable**
will represent the **current key**, not the **current value**.

 

for loops
=========

```python
band = {
  "johnny": "plays drums",
  "joey": "plays guitar",
  "markee": "sings",
  "dee-dee": "plays bass-guitar"
}

for member in band:
  print(member + " " + band[member] + " in The Ramones")
```

for loops
=========

Exercises
=========

``` {.tex}
1. Create a function that receives a text and returns the frequency of
   each word in the text (as a dictionary).

2. Create a function that uses the previously generated dictionary and
   prints a bars diagram of the frequencies.  For example, the
   following:

   dictionary = {"a": 4, "hello": 1, "world": 3, "another": 2}
   diagram(dictionary)

   should print:

   a       | ****
   hello   | *
   world   | ***
   another | **  
```
