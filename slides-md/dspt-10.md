---
title: Data Structures & Programmatic Thinking
subtitle: Session 10
author: Pepe García
email: jgarciah@faculty.ie.edu
date: 2020-09-18
lang: en
---

# Mutating lists

Lists are mutable values, and they provide functionality to add, delete,
and update elements

# Updating elements in the list

To update an element inside the list, we use a syntax similar to the one
for declaring variables, but using the brackets and the index we refer
to.

```python
numbers = [1,2,4]
numbers[2] = 3
print(numbers) # prints [1,2,3]
```

. . .

\begin{exampleblock}{Demo}
\end{exampleblock}

# Appending elements to the list

To add a new element to the end of the list we use the append() method
on it.

```python
numbers = [1,2,3]
numbers.append(4)
print(numbers) # prints [1,2,3,4]
```

. . .

\begin{exampleblock}{Demo}
\end{exampleblock}

# Inserting elements in the list

There\'s an alternative way of adding new elements to the list, and
it\'s using the insert() method on it:

```python
words = ["hello","my","friends"]
words.insert(2, "dear")
print(words) # prints ["hello", "my", "dear", "friends"]
```

The difference between this and append is that with insert we can choose
where to put it by using the target index

. . .

\begin{exampleblock}{Demo}
\end{exampleblock}

# Removing elements from the list

In order to remove an element from a list, we should use the .pop()
method, and pass the index of the element we want to remove

```python
words = ["hello","my","friend"]
words.pop(1)
print(words)
```

. . .

\begin{exampleblock}{Demo}
\end{exampleblock}

# For loops

For loops are simpler than while loops. They iterate over elements in a
list.  They loop once for every element in the list.

. . .

```python
for <iteration_variable> in <list>:
    <body>
```

In each iteration, we will have a new value for the **`iteration_variable`**.

. . .

\begin{exampleblock}{Demo}
Let's see an example for adding all numbers in a list
\end{exampleblock}

# Practice

##

Create a function **`to_string`** that receives a list of strings,
concatenates all of them and returns it as a single string.

# Checkpoint

\begin{exampleblock}{Checkpoint}
Is everybody following so far?  Is there any question, comment?
\end{exampleblock}

# Dictionaries

Dictionaries are another kind of collection in Python.  Dictionaries 
map keys to values.

# Creating dictionaries

We use curly brackets **{}** to declare dictionaries.

```python
translations = {
    "es": "Hola!",
    "it": "Ciao!",
    "en": "Hello!"
}
```

colon for separating key and value

comma for separating entries

# Creating dictionaries

We can also create empty dictionaries

```python
translations = {}
```

# Creating dictionaries

# Adding elements

We add elements to dictionaries given their specific index:

```python
translations = {}
translations["en"] = "Hello"
translations["it"] = "Ciao"
translations["es"] = "Hola"
```

# Updating elements

we always can change a value in the dictionary by re-assigning the key

```python
translations = {}
translations["en"] = "Hello"
translations["en"] = "WHATUP!"
```

# Updating elements

# Deleting elements

We can delete an element of the dictionary using the **pop** method

```python
translations = {}
translations["en"] = "Hello"
translations.pop("en")
```

# Deleting elements

# Getting all keys or values

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

# Getting all keys or values

# for loops

In the same way we used **for** loops to iterate over elements of a
list, we can use them to iterate over elements of a dictionary.

 

The difference is that, with dictionaries, the **iteration variable**
will represent the **current key**, not the **current value**.

# for loops

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
