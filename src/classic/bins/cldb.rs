use std::env;
use clvm_tools_rs::classic::clvm_tools::cmds::cldb;

fn main() {
    env_logger::init();

    let args: Vec<String> = env::args().collect();
    cldb(&mut std::io::stdout(), &args);
}
