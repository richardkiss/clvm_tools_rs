use clvm_tools_rs::classic::clvm_tools::cmds::cldb;
use std::env;

fn main() {
    env_logger::init();

    let args: Vec<String> = env::args().collect();
    cldb(&mut std::io::stdout(), &args);
}
