#!/bin/sh

# path to the executable
filepath="/usr/local/bin/coqpilot-server"

# get current directory
current_dir=$(pwd)
printf "\033[0;32mCreating a shell script at $filepath...\033[0m\n"

# create the bash script
cat > "$filepath" << EOF
#!/bin/bash
run_root=\$(pwd)
cd $current_dir
npm run server -- SERVER_RUN_ROOT=\$run_root
EOF

printf "\033[0;32mMaking the script executable...\033[0m\n"
chmod +x $filepath

printf "\e[33mThe command 'coqpilot-server' has been created! \033[0m✅\n"
printf "\033[0;32mNow, you can run 'coqpilot-server' from any location.\033[0m\n"