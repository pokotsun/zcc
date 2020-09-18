use crate::parser::*;
use crate::util::error;
//
// Code Generator
//

const REGISTERS: [&str; 6] = ["%r10", "%r11", "%r12", "%r13", "%r14", "%r15"];
pub fn reg(idx: usize) -> &'static str {
    REGISTERS
        .get(idx)
        .expect(&format!("register out of range: {}", idx))
}

fn gen_expr(node: Node, mut top: usize) -> usize {
    match node.kind {
        NodeKind::Num(val) => {
            println!("  mov ${}, {}", val, reg(top));
            top += 1;
        }
        NodeKind::Unary(_, _) => {}
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

// return register top index
fn gen_stmt(node: Node) -> usize {
    match node.kind {
        NodeKind::Unary(op, node) => {
            match op {
                UnaryOp::Return => {
                    let top = gen_expr(*node, 0) - 1;
                    // Set the result of the expression to RAX so that
                    // the result becomes a return value of this function.
                    println!("  mov {}, %rax", reg(top));
                    println!("  jmp .L.return");

                    top
                }
                UnaryOp::ExprStmt => gen_expr(*node, 0) - 1,
            }
        }
        _ => {
            error("invalid statement.");
            100 as usize
        }
    }
}

pub fn codegen(nodes: Vec<Node>) {
    println!(".globl main");
    println!("main:");

    // Save callee-saved registers
    println!("  push %r12");
    println!("  push %r13");
    println!("  push %r14");
    println!("  push %r15");

    for node in nodes {
        let top = gen_stmt(node);
        if top != 0 {
            error("register top is invalid.");
        }
    }

    println!(".L.return:");
    println!("  pop %r15");
    println!("  pop %r14");
    println!("  pop %r13");
    println!("  pop %r12");

    println!("  ret");
}
