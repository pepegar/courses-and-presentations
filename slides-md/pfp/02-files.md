---
title: Programming fundamentals with Python
subtitle: Using files with Python
author: Pepe García <jgarciah@faculty.ie.edu>
email: jgarciah@faculty.ie.edu
---

Plan for today

>- Learn about handling files with Python
>- Learn about CSV
>- Learn about JSON

# data for today

## Session 3 & 4 repository

All materials for today's session will be in
[**`https://github.com/mcsbt-pfp-2022/sessions-3-and-4`**](https://github.com/mcsbt-pfp-2022/sessions-3-and-4).
Clone it if you want to have it in your computer.

```bash


$ cd Desktop # or any other folder you'd like to put this repo
$ git clone https://github.com/mcsbt-pfp-2022/sessions-3-and-4
```

# the **open** function

We can use **open()** to open a file in Python, we only need to pass
the path of the file we want to open.  Let's say there's a file named
hello.txt in my desktop that I want to open and read from Python, I
can do it as follows:

. . .

```python
file = open("hello.txt")
```

# Reading the contents of a file

Now that we know how to open and close files, we can read the contents
of a file.  Let's do that line by line.

. . .

```python
file = open("hello.txt")

for line in file:
    print(line)

file.close()
```

. . .

As you can see, we're treating `file` as a list of lines.

# Interlude, **with**

there is a useful Python keyword that one can use to make sure that
the file will always be closed, **with**:

. . .

```python
with open("file_path") as file:

    for line in file:
        #do something with line
        print(line)
```

# Handling files. modes

When opening a file, we can choose in which **mode** we open it
depending on how we're going to use it.

![file modes](./img/file-modes.png){width=100%}

# Writing files

We can write into files in a way similar to the one used for reading
them.

. . .

```python
with open('goodbye.txt', 'w') as file:
    file.write("goodbye y'all!")
```

# CSV

CSV is a data interchange format used for representing tabular data.

# CSV - how does it look like?

::: columns

:::: column

. . .

>- **syntax** is, just the values separated by commas
>- We separate entries by adding a new line
::::

:::: column
![](./img/csv.png)
::::

:::


# CSV files - reading

The **csv** library is based on the idea of readers and writers.  One
can read all lines in a file like so:

::: columns

:::: column

```python
import csv

with open("file.csv") as f:
    reader = csv.reader(f)
    for line in reader:
        print(line)  #line is a list
```

::::

:::: column

. . .

>- first we open the file normally
>- Then we create a reader using **csv.reader()**
>- Finally, we operate with the reader

::::

:::

# CSV files - writing

writing is not very different from reading:

```python
lines = [
  ["asdf", "qwer"],
  ["hello", "world"]
]

with open("file.csv", "a") as f:
    writer = csv.writer(f)
    for line in lines:
        writer.writerow(line)
```

# CSV Files - exercise

##

Let's remember how to use CSV files.  There is a CSV in
**`data/data.csv`**.  Let's create a Python function that returns all
the emails from the users in the file.

# Plan for today

- Files refresher
- CSV refresher
- Learn about JSON

# JSON

::: columns

:::: column

JSON (http://json.org) is a data interchange format, like CSV.  The
name JSON stands for **Javascript Object Notation**, because the way
of writing it is very similar to Javascript.

The main difference is that **JSON can represent arbitrary data, not
only tabular data**.

::::

:::: column

![](./img/json.png){width=100px}

::::

:::

# JSON - how does it look like?

::: columns

:::: column
![](./img/json-example.png)
::::

:::: column

. . .

>- **syntax** similar to Python data structures
>- supports **primitive** datatypes (**int, str, bool, float**).
>- supports collections of elements with **lists**
>- supports mapping of elements with **dictionaries**
::::

:::

# JSON

JSON can contain

::: columns

:::: column

```json
[1, 2, 3]
1
true
"potatoes"
4.77
null
{"first":"Pepe","last":"Garcia"}
```

::::

:::: column

. . .

>- lists
>- integers
>- booleans
>- strings
>- floats
>- null (an empty value)
>- dictionaries

::::

:::

# JSON

JSON is very similar to how we declare our data in Python but the cool
thing about it is that it can be used **from any language**.  In
Python we will be able to use JSON using the **`json`** module


```python
import json
```

# JSON - reading JSON data in Python

As with other formats we've seen so far, in order to operate with json
files we will first **open()** the file.

. . .

::: {.columns}

:::: {.column}

```python
import json

with open("data.json") as file:
    json_data = json.load(file)

    for key in json_data:
        print(key)
```
::::

:::: {.column width=30%}

**`json.load`** is a function from the json module that
takes a **file object** as parameter and returns the contents of that
file **parsed as JSON**.

::::

:::

# JSON - writing JSON files

The process of writing JSON files is similar to what we know already.

::: {.columns}

:::: {.column width=55%}

```python
import json

data = {
  "name": "Pepe",
  "last_name": "Garcia"
}

with open("data.json", "w") as file:
    json.dump(data, file)
```

::::

:::: {.column width=45%}

As you can see, we're calling **`json.dump`** from the **`json`**
library, and passing first the data we want to write to the file and
then the file object as parameters.

::::

:::

# Homework

You will find the data files for these exercises in the repository

- Let's get personal data from the person represented in
  **`luke.json`**.  Print the **`name`**, **`height`**,
  **`eye_color`**, and **`mass`**.
- Let's create a **format conversor**. Our function
  **`convert_format`** will read all the data from **`data/data.csv`** and
  write it to a new **JSON** file named **`converted.json`**
