use std::io;

fn check_value(value: u64) -> bool {
    match value {
        0xFFFF
        | 0xFFFFFF
        | 0xFFFFFFFF
        | 0xFFFFFFFFFF
        | 0xFFFFFFFFFFFF
        | 0xFFFFFFFFFFFFFF
        | 0xFFFFFFFFFFFFFFFF => false,
        v if v <= 0xFF => false,
        v if !v <= 0xFF => false,
        _ => true,
    }
}

fn main() {
    println!("input:");

    let mut input = String::new();
    io::stdin()
        .read_line(&mut input)
        .expect("failed");

    let value = input.trim();
    let value = if value.starts_with("0x") || value.starts_with("0X") {
        u64::from_str_radix(&value[2..], 16)
    } else {
        value.parse::<u64>()
    };

    match value {
        Ok(num) => {
            let result = check_value(num);
            println!("output:{}", result);
        }
        Err(_) => {
            println!("invalid input!");
        }
    }
}
