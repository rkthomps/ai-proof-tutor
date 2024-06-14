# Proofessor
## Description
The Proofessor is an AI-based tutor for students learning to write informal mathematical proofs, specifically in UC San Diego's CSE 20 Discrete Mathematics course. The tool leverages GPT-4 through few-shot prompting, auto-formalizes student-written proofs, and allows for multi-round interaction with the goal of providing a more accessible and reliable tutoring tool as compared to office hours and ChatGPT. We dissected the proof-writing process into five stages, ranging from not understanding the problem statement to having a complete correct or incorrect proof attempt, such that students can input the theorem they are working on and the stage they are at into the tool. The theorem and stage are specified in a few-shot prompt to GPT-4 when a student submits their question or progress, and the tool responds with feedback. We also integrated the auto-formalization of students' proofs into Lean, a language for formal theorem proving, to provide a second level of verification to the tool's responses. Upon evaluation of our tool against the GPT-4 baseline, we saw improvements in the tool's ability to provide more relevant responses and those that do not reveal the proof's correct answer. Evaluating the tool's auto-formalization, we found that the proof translations were not always faithful. Ultimately, we hope that the Proofessor can be used to help students as they learn to write proofs.

## Setup
### Clone the Project
- Open up your terminal. Navigate to the directory where you want this project to be located. For example, if I want this project to be located in the directory "/home/bob/ai-proof-tutor", I should type "cd /home/bob".
- Run `git clone https://github.com/rkthomps/ai-proof-tutor` to get a copy of this repository onto your computer.
- Now, there should be a new directory called "ai-proof-tutor". Change into that directory with `cd ai-proof-tutor`.
- Great! You've got a copy of this project on your machine!

### Set up your Python Environment
- Make sure you have Python installed on your machine. You can check this by running `python --version` or `python3 --version`. It is good practice to make a sort of sandbox environment for projects. In this case, run `python3 -m venv venv`. That will make a sandbox called `venv` for our project.
- To activate our virtual environment (sandbox) run `source venv/bin/activate` on Mac/Linux. Run `venv\Scripts\activate` on Windows. Make sure you run this command whenever you want to run the tutor. 
- Now you are ready to install the necessary packages for this project! Run `pip3 install -e .` to install the necessary packages.

### Lean4 
- Already installed -- check out the documentation linked below and PROOFS directory for configuration. (Not recommended to change anything within this dir)
- If you need any change within formal proofs configuration: https://leanprover-community.github.io/get_started.html
- (Optional): learn more about mathlib library to simplify the theorem proving process: https://github.com/leanprover-community/mathlib4


### Adding your OpenAi Keys
Set the environment variable `OPENAI_API_KEY` to your API key. Set the environment variable `OPENAI_ORG_KEY` to your org key.
You can create an API key [here](https://platform.openai.com/api-keys). You can find your organization key [here](https://platform.openai.com/account/organization). 

Warning for Windows Users: the def get_client() will try to access your OS environmental variables. Doing so, it can possibly get flagged by anti-virus on Windows 10 and prevent tool from working. If that happens, delete def_client() and refactor your code by using OPENAI_API_KEY and OPENAI_ORG_KEY as global variables. Reach out to github: Babuka6 if you need more help with Windows setup.   

### Running the Proof Tutor
- You are now ready to run the proof tutor!
- To run the tool, in the "ai-proof-tutor" directory", run `python3 src/tutor/give_advice.py`.
- It would give you a local URL and a public URL, which allows you to run locally or publicly.

## Contributing
Pushing your changes to the repository requires these steps:
1. You can run `git status` to see the state of the local repository.
2. You can run `git add .` to add everything under the current directory. You can also run `git add <file>` to add a specific file to the staging area.
3. You can run `git commit -m <commit message>` to add a "commit" to the repository. <commit message> should describe the changes that you made.
4. You can run `git push -u origin main` to push your changes back to the central repository. Beware that this will update the code for everyone.

Getting updated changes requires these steps:
- `git pull`

If you want to push some experimental changes, you can create a new branch. 
- To make a new branch, run `git checkout -B my-new-branch`.
- To see which branch you are on, run `git branch`. When you run `git commit` it will make a commit only for the branch you are on.
- To switch branches run `git checkout main` to switch to main or `git checkout my-new-branch` to switch to `my-new-branch`.
- To push your branch to the central repository, commit your changes to `my-new-branch` and run `git push -u origin my-new-branch`
- Then, others can review your changes and decide whether they want to merge them into the central code base. 
