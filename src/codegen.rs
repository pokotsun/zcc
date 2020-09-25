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

fn gen_addr(node: &Node, top: usize) -> Result<usize, String> {
    match &node.kind {
        NodeKind::Var { var } => {
            println!("  lea -{}(%rbp), {}", var.offset, reg(top));
            Ok(top + 1)
        }
        _ => {
            error("");
            Err("NodeKind is Invalid".to_string())
        }
    }
}

fn load(top: usize) {
    println!("  mov ({}), {}", reg(top - 1), reg(top - 1));
}

fn store(top: usize) -> usize {
    println!("  mov {}, ({})", reg(top - 2), reg(top - 1));
    top - 1
}

fn gen_expr(node: &Node, mut top: usize) -> usize {
    match &node.kind {
        NodeKind::Num(val) => {
            println!("  mov ${}, {}", val, reg(top));
            top += 1;
        }
        NodeKind::Unary(_, _) => {}
        NodeKind::Bin { op, lhs, rhs } if matches!(op, BinOp::Assign) => {
            top = gen_expr(&*rhs, top);
            top = gen_addr(&*lhs, top).unwrap();
            top = store(top);
        }
        NodeKind::Bin { op, lhs, rhs } => {
            top = gen_expr(&*rhs, gen_expr(&*lhs, top));
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
                _ => error("Invalid BinOp, probably Assign"),
            }
        }
        NodeKind::Var { var: _ } => {
            top = gen_addr(&node, top).unwrap();
            load(top);
        }
    }
    top
}

// return register top index
fn gen_stmt(node: &Node) -> usize {
    match &node.kind {
        NodeKind::Unary(op, node) => {
            match op {
                UnaryOp::Return => {
                    let top = gen_expr(&*node, 0) - 1;
                    // Set the result of the expression to RAX so that
                    // the result becomes a return value of this function.
                    println!("  mov {}, %rax", reg(top));
                    println!("  jmp .L.return");

                    top
                }
                UnaryOp::ExprStmt => gen_expr(&*node, 0) - 1,
            }
        }
        _ => {
            error("invalid statement.");
            100 as usize
        }
    }
}

pub fn codegen(prog: &Function) {
    println!(".globl main");
    println!("main:");

    // Prologue %r12-15 are callee-saved registers.
    println!("  push %rbp");
    println!("  mov %rsp, %rbp"); // 現在のrspをrbpにセット
    println!("  sub ${}, %rsp", prog.stack_size); // 関数の
    println!("  mov %r12, -8(%rbp)");
    println!("  mov %r13, -16(%rbp)");
    println!("  mov %r14, -24(%rbp)");
    println!("  mov %r15, -32(%rbp)");

    for node in &prog.nodes {
        let top = gen_stmt(&node);
        if top != 0 {
            error("register top is invalid.");
        }
    }

    // Epilogue
    println!(".L.return:");
    println!("  mov -8(%rbp), %r12");
    println!("  mov -16(%rbp), %r13");
    println!("  mov -24(%rbp), %r14");
    println!("  mov -32(%rbp), %r15");
    println!("  mov %rbp, %rsp"); // rbpをrspにセットすることで今の関数のreturnアドレスにrspを移動
    println!("  pop %rbp");
    // call命令はcallの次の命令のアドレスをスタックに積むため
    // retすることでそのスタック上の値を読み出しcallの次の命令に移動
    println!("  ret");
}
