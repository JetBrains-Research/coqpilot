# 🖥️ Remote Rango Server Setup (GPU Inference over SSH)

This guide describes how to run the Rango model inference server on a remote GPU machine (e.g., using `RunPod`) and connect to it via SSH for use with CoqPilot.

## Table of Contents

- 🔧 [One-Time Setup](#one-time-setup)
- 🚀 [Running the Rango Server](#running-the-rango-server)
- 🌟 [Using Rango from CoqPilot](#using-rango-from-coqpilot)

## One-Time Setup

These steps are required once per new remote machine:

1. **Add your SSH key to RunPod**  
   Go to [RunPod SSH Keys](https://www.runpod.io/console/user/settings) and paste your public key.<br/>
   Or, manually add it via web terminal:

    ```bash
    echo "<your-public-key>" >> /root/.ssh/authorized_keys
    ```

2. **Rent a pod**  
   Choose a configuration like "1 x RTX 4090" at  
   https://www.runpod.io/console/pods

3. **Set up SSH access from your local machine**  
   Use the "SSH over exposed TCP" info provided in the pod UI.  
   Append the following to your `~/.ssh/config` on your local machine:

    ```
    Host zebra
      HostName <POD_IP>
      User root
      Port <EXPOSED_PORT>
    ```

4. **Run the remote setup script**  
   SSH into your pod and execute:

    ```bash
    bash -c "$(curl -fsSL https://raw.githubusercontent.com/JetBrains-Research/coqpilot/main/scripts/rango/setup-remote-rango.sh)"
    ```

    Or, if you've cloned the repo:

    ```bash
    ./coqpilot/scripts/rango/setup-remote-rango.sh
    ```

This script will:

- Install system dependencies
- Attempt to install `pyenv` if needed
- Clone CoqPilot if not already present
- Set up Rango and download the local model

## Running the Rango Server

Every time you want to run the inference server:

1. **Forward port 5000 (default one) from the remote to your local machine**  
   On your local machine:

    ```bash
    ssh -L 5000:localhost:5000 zebra
    ```

2. **Start the server on the remote machine**
    ```bash
    cd ~/rango
    export OPENAI_API_KEY="" # is not really used, Rango just needs it to be declared
    pyenv shell 3.11
    source ./venv/bin/activate
    exec python3 src/model_deployment/tactic_gen_server_remote.py \
        decoder-local models/deepseek-bm25-proof-tfidf-proj-thm-prem-final/checkpoint-54500 \
        0 5000
    ```
    or, in one command:
    ```bash
    cd ~/rango && export OPENAI_API_KEY="" && pyenv shell 3.11 && source ./venv/bin/activate && exec python3 src/model_deployment/tactic_gen_server_remote.py \
        decoder-local models/deepseek-bm25-proof-tfidf-proj-thm-prem-final/checkpoint-54500 \
        0 5000
    ```

## Using Rango from CoqPilot

Once the Rango server is running, CoqPilot can generate proofs via it.

In CoqPilot, simply declare Rango model with `mode: "remote"` and you're good to go!
