# <MAKE A TITLE>
## Make a Description

## Setup
### Clone the Project
- Open up your terminal. Navigate to the directory where you want this project to be located. For example, if I want this project to be located in the directory "/home/bob/ai-proof-tutor", I should type "cd /home/bob".
- Run `git clone https://github.com/rkthomps/ai-proof-tutor` to get a copy of this repository onto your computer.
- Now, there should be a new directory called "ai-proof-tutor". Change into that directory with `cd ai-proof-tutor`.
- Great! You've got a copy of this project on your machine!

### Set up your Python Environment
- Make sure you have python installed on your machine. You can check this by running `python --version` or `python3 --version`. It is good practice to make a sort of sandbox environment for projects. In this case, run `python3 -m venv venv`. That will make a sandbox called `venv` for our project.
- To activate our virtual environment (sandbox) run `source venv/bin/activate` on Mac/Linux. Run `venv\Scripts\activate` on Windows. Make sure you run this command whenver you want to run the tutor. 
- Now you are ready to install the necessary packages for this project! Run `pip3 install -e .` to install the necessary packages.

### Adding your OpenAi Keys
Set the environment variable `OPENAI_API_KEY` to your api key. Set the environment variable `OPENAI_ORG_KEY` to your org key.
You can create an api key [here](https://platform.openai.com/api-keys). You can find your organization key [here](https://platform.openai.com/account/organization). 

### Running the Proof Tutor
- You are now ready to run the bare-bones proof tutor!
- The proof tutor needs three things:
  - A text file containing the theorem statement.
  - A text file containing the correct proof.
  - A text file containing a proof attempt.
  given these things, the tutor comes up with a response and prints it to the screen. Right now the tutor is not so good. You can see that by running\
`python3 src/tutor/give_advice.py theorems/example/statement.txt theorems/example/attempt.txt theorems/example/correct.txt`\
This command runs the tutor on a silly theorem defined in [theorems/example/statement.txt](theorems/example/statement.txt), with a proof attempt in [theorems/example/attempt](theorems/example/attempt.txt) and a ground truth proof defined in [theorems/example/correct.txt](theorems/example/correct.txt).

You should get an output similar to the following:
```
Theorem Statement:
Prove that the sky is blue.

Correct Proof:
The sky is blue because you and I see a blue sky.

Proof Attempt:
The sky is blue because I see a blue sky.

Response:
Hello! How can I assist you today?
```

## Contributing
Pushing your changes to the repository requires these steps:
1. You can run `git status` to see the state of the local repository.
2. You can run `git add .` to add everything under the current directory. You can also run `git add <file>` to add a specific file to the staging area.
3. You can run `git commit -m <commit message>` to add a "commit" to the repository. <commit message> should describe the changes that you made.
4. You can run `git push -u origin main` to push your changes back to the central repository. Beware that this will update the code for everyone.

Getting updated changes requires these steps:
- `git pull`

If you want to push some expirimental changes, you can create a new branch. 
- To make a new branch, run `git checkout -B my-new-branch`.
- To see which branch you are on, run `git branch`. When you run `git commit` it will make a commit only for the branch you are on.
- To switch branches run `git checkout main` to switch to main or `git checkout my-new-branch` to switch to `my-new-branch`.
- To push your branch to the central repository, commit your changes to `my-new-branch` and run `git push -u origin my-new-branch`
- Then, others can review your changes and decide whether they want to merge them into the central code base. 




