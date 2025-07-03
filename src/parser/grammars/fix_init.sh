#\!/bin/bash

# Rules that need @init blocks added
rules_no_init=(
    "command_topic returns \[cmd::CommandTopic_ptr res\]"
    "command returns \[cmd::Command_ptr res\]"
    "help_command returns \[cmd::Command_ptr res\]"
    "help_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "do_command returns \[cmd::Command_ptr res\]"
    "do_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "echo_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "last_command returns \[cmd::Command_ptr res\]"
    "last_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "on_command returns \[cmd::Command_ptr res\]"
    "on_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "time_command returns \[cmd::Command_ptr res\]"
    "time_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "read_model_command returns \[cmd::Command_ptr res\]"
    "read_model_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "read_trace_command returns \[cmd::Command_ptr res\]"
    "read_trace_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "dump_model_command returns \[cmd::Command_ptr res\]"
    "dump_model_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "check_init_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "diameter_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "reach_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "select_trace_topic returns \[cmd::CommandTopic_ptr res\]"
    "check_trans_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "list_traces_command returns \[cmd::Command_ptr res\]"
    "list_traces_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "dump_traces_command returns \[cmd::Command_ptr res\]"
    "dump_traces_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "dup_trace_command returns \[cmd::Command_ptr res\]"
    "dup_trace_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "pick_state_command returns \[cmd::Command_ptr res\]"
    "pick_state_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "simulate_command returns \[cmd::Command_ptr res\]"
    "simulate_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "get_command returns \[cmd::Command_ptr res\]"
    "get_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "set_command returns \[cmd::Command_ptr res\]"
    "set_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "clear_command returns \[cmd::Command_ptr res\]"
    "clear_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "quit_command returns \[cmd::Command_ptr res\]"
    "quit_command_topic returns \[cmd::CommandTopic_ptr res\]"
    "pcchar_quoted_string returns \[pconst_char res\]"
)

for rule in "${rules_no_init[@]}"; do
    sed -i "/$rule/ a\\@init { \$res = NULL; }" smv.g
done

echo "Fixed rules without @init blocks"
