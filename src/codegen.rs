use crate::parser::*;
//
// Code Generator
//

const REGISTERS: [&str; 6] = ["%r10", "%r11", "%r12", "%r13", "%r14", "%r15"];
pub fn reg(idx: usize) -> &'static str {
    REGISTERS
        .get(idx)
        .expect(&format!("register out of range: {}", idx))
}

pub fn gen_expr(node: Node, mut top: usize) -> usize {
    match node.kind {
        NodeKind::Num(val) => {
            println!("  mov ${}, {}", val, reg(top));
            top += 1;
        }
        NodeKind::Bin { op, lhs, rhs } => {
            top = gen_expr(*rhs, gen_expr(*lhs, top));
            let rd = reg(top - 2);
            let rs = reg(top - 1);
            top -= 1;

            match op {
                BinOp::Add => println!("  add {}, {}", rs, rd),
                BinOp::Sub => println!("  sub {}, {}", rs, rd),
                BinOp::Mul => println!("  imul {}, {}", rs, rd),
                BinOp::Div => {
                    println!("  mov {}, %rax", rd);
                    println!("  cqo");
                    println!("  idiv {}", rs);
                    println!("  mov %rax, {}", rd);
                }
                BinOp::Equal => {
                    println!("  cmp {}, {}", rs, rd);
                    println!("  sete %al");
                    println!("  movzb %al, {}", rd);
                }
                BinOp::NEqual => {
                    println!("  cmp {}, {}", rs, rd);
                    println!("  setne %al");
                    println!("  movzb %al, {}", rd);
                }
                BinOp::Lt => {
                    println!("  cmp {}, {}", rs, rd);
                    println!("  setl %al");
                    println!("  movzb %al, {}", rd);
                }
                BinOp::Le => {
                    println!("  cmp {}, {}", rs, rd);
                    println!("  setle %al");
                    println!("  movzb %al, {}", rd);
                }
            }
        }
    }
    top
}
