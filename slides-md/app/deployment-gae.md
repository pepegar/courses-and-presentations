---
title: Advanced Programming with Python
subtitle: Deploying Python apps
author: Pepe García <jgarciah@faculty.ie.edu>
email: jgarciah@faculty.ie.edu
---

# Deployment

When we talk about deployment, we mean running our application
somewhere in the internet.

In this case we will run it on **Google App Engine**.

# Google App Engine

:::columns
::::column

Google App Engine (**GAE**) is a PaaS Platform by Google Cloud.

We can host applications written in a range of different programming
languages, but we'll focus on Python ourselves.

It's similar to other services such as **Heroku**, **Elastic
Beanstalk**, **Engineyard**.

::::
::::column

![GAE logo](https://miro.medium.com/max/993/1*NsjhnM3r0Bsus_41jrkGwg.png)

::::
:::

# **`gcloud`**

We will interact with Google Cloud using the **`gcloud`** sdk.  It's a
command line interface that provides access to all features in Google
Cloud.

&nbsp;

[https://cloud.google.com/sdk/gcloud](https://cloud.google.com/sdk/gcloud)

# Practice

In this practice we will create a toy Flask application and deploy it
to Google App Engine.

# Practice

## steps

- Authenticate with **`gcloud`**
- Create a project in **`gcloud`**
- Create a simple flask application
- Create needed files
- Deploying the app in Google App Engine

# Practice

## steps

- **Authenticate with `gcloud`**
- Create a project in `gcloud`
- Create a simple flask application
- Create needed files
- Deploying the app in Google App Engine

# Practice

```sh
$ gcloud auth login
```

# Practice

## steps

- Authenticate with **`gcloud`**
- **Create a project in `gcloud`**
- Create a simple flask application
- Create needed files
- Deploying the app in Google App Engine

# Practice. Create project

We can have more than one project under the same Google account
running on Google Cloud.  We tell them appart using projects.

# Practice. Create project

```sh
$ gcloud projects create mcsbt-app-session-13-pepegar
```

. . .

\begin{alertblock}{Attention}
the id we give to the project must be unique
\end{alertblock}

# Practice. Create project

```sh
$ gcloud projects list
PROJECT_ID                    NAME                   PROJECT_NUMBER
mcsbt-app-session-13-pepegar  mcsbt-flask-example-1  421790155851
```

# Practice. Create project

We'll also configure the project as the current one:

```sh
$ gcloud config set project mcsbt-app-session-13-pepegar
```

# Practice

## Checkpoint

At this point we should have:

```sh
$ gcloud projects list
PROJECT_ID                    NAME                   PROJECT_NUMBER
mcsbt-app-session-13-pepegar  mcsbt-flask-example-1  421790155851

$ gcloud config get-value project
mcsbt-flask-example-1
```

# Practice

## steps

- Authenticate with **`gcloud`**
- Create a project in **`gcloud`**
- **Create a simple flask application**
- Create needed files
- Deploying the app in Google App Engine

# Practice. Flask application

Now, let's create a **very simple** Flask app (**`main.py`**):

. . .

```python
from flask import Flask

app = Flask(__name__)

@app.route("/")
def index():
    return "Hello, Appengine!"

# app.run()
```

. . .

\begin{alertblock}{Attention}
appengine will look for a variable named app and run it, we must not do it manually.
\end{alertblock}


# Practice

## Checkpoint

Now there should be a **`main.py`** file in our folder, **without the
`app.run()`**.  Remember that **GAE** is gonna look for the variable
called app for us, and run it.  We won't need to run it manually.

```sh
$ ls
main.py
```

# Practice

## steps

- Authenticate with **`gcloud`**
- Create a project in **`gcloud`**
- Create a simple flask application
- **Create needed files**
- Deploying the app in Google App Engine

# Practice. Creating the needed files

There are two files we will need to create in our project in order to
make it run on **GAE**:

&nbsp;

. . .

- `requirements.txt`
- `app.yaml`

# Practice. Creating the needed files

**`requirements.txt`** describes the dependencies of our application
and their versions.  In our case, it's only going to be Flask.

```txt
Flask==1.1.2
```

# Practice. Creating the needed files

**`app.yaml`** declares information needed for Google App Engine.  In
our case, we'll just specify the version of python we need.

```yaml
runtime: python39
```

# Practice

## Checkpoint

```sh
$ ls
app.yaml              main.py          requirements.txt
```
# Practice

## steps

- Authenticate with **`gcloud`**
- Create a project in **`gcloud`**
- Create a simple flask application
- Create needed files
- **Deploying the app in Google App Engine**

# Practice. Deploying our app to GAE

```sh
$ gcloud app create

...

Please enter your numeric choice:  8

Creating App Engine application in project [pepegar-test-1] and region [europe-west]....done.
Success! The app is now created. Please use `gcloud app deploy` to deploy your first app.

```

# Practice. Deploying our app to GAE

```sh
$ gcloud app deploy

...

Do you want to continue (Y/n)?  Y

Beginning deployment of service [default]...
╔════════════════════════════════════════════════════════════╗
╠═ Uploading 3 files to Google Cloud Storage                ═╣
╚════════════════════════════════════════════════════════════╝
File upload done.
Updating service [default]...done.
Setting traffic split for service [default]...done.
Deployed service [default] to [https://pepegar-test-1.ew.r.appspot.com]

You can stream logs from the command line by running:
  $ gcloud app logs tail -s default

To view your application in the web browser run:
  $ gcloud app browse
```

# Practice. Deploying our app to GAE

\begin{alertblock}{Attention}
With a real GCP account, last command may fail because of Google Cloud Build, you'll need to activate it.
\end{alertblock}
