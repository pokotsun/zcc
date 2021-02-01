use std::unimplemented;

use crate::parser::*;
use crate::types::{Type, TypeKind};
use crate::util::error;
use crate::{
    node::{BinOp, Node, NodeKind, UnaryOp, VarType},
    util::LabelCounter,
};
//
// Code Generator
//

const REGISTERS: [&str; 6] = ["%r10", "%r11", "%r12", "%r13", "%r14", "%r15"];
const ARG_REGISTERS8: [&str; 6] = ["%dil", "%sil", "%dl", "%cl", "%r8b", "%r9b"];
const ARG_REGISTERS64: [&str; 6] = ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"];

fn reg_access(reg: [&'static str; 6], idx: usize) -> &'static str {
    reg.get(idx)
        .expect(&format!("register out of range: {}", idx))
}

fn reg(idx: usize) -> &'static str {
    reg_access(REGISTERS, idx)
}

fn arg_reg8(idx: usize) -> &'static str {
    reg_access(ARG_REGISTERS8, idx)
}

fn arg_reg64(idx: usize) -> &'static str {
    reg_access(ARG_REGISTERS64, idx)
}

fn gen_addr(node: &Node, top: usize) -> Result<usize, String> {
    match &node.kind {
        NodeKind::Var { var } => {
            match var.var_ty.clone() {
                VarType::Local(offset) => {
                    println!("  lea -{}(%rbp), {}", offset.get(), reg(top));
                }
                VarType::Global(_) => {
                    println!("  mov ${}, {}", var.name, reg(top));
                    // このコンパイラの場合, マイナス方向にデータが生えるため
                    // 最初のデータまでのoffsetをとってやる
                    // if let TypeKind::Arr { .. } = var.ty.kind.as_ref() {
                    //     println!("  add ${}, {}", var.ty.size - 1, reg(top));
                    // }
                }
            }
            Ok(top + 1)
        }
        NodeKind::Unary(UnaryOp::Deref, child) => {
            let top = gen_expr(child, top);
            Ok(top)
        }
        _ => Err(format!("NodeKind is Invalid: {:?}, expected Var", node)),
    }
}

fn load(ty: Type, top: usize) {
    let r = reg(top - 1);
    match ty.kind.as_ref() {
        TypeKind::Arr { .. } => {
            // If it is an array, do nothing because in general we can't load
            // an entire array to a register. As a result, the result of an
            // evaluation of an array becomes not the array itself but the
            // address of the array. In other words, this is where "array is
            // automatically converted to a pointer to the first element of
            // the array in C" occurs.
            return;
        }
        TypeKind::Char => {
            println!("  movsbq ({}), {}", r, r);
        }
        _ => {
            println!("  mov ({}), {}", r, r);
        }
    }
}

fn store(ty: Type, top: usize) -> usize {
    let rd = reg(top - 1);
    let rs = reg(top - 2);
    match ty.kind.as_ref() {
        TypeKind::Char => {
            println!("  mov {}b, ({})", rs, rd);
        }
        _ => {
            println!("  mov {}, ({})", rs, rd);
        }
    }
    top - 1
}

fn gen_expr(node: &Node, mut top: usize) -> usize {
    match &node.kind {
        NodeKind::Num(val) => {
            println!("  mov ${}, {}", val, reg(top));
            top += 1;
        }
        NodeKind::Bin {
            op: BinOp::Assign,
            lhs,
            rhs,
        } => {
            if let TypeKind::Arr { .. } = node.get_type().kind.as_ref() {
                unimplemented!("array will not be assigned.")
            }
            top = gen_expr(&*rhs, top);
            top = gen_addr(&*lhs, top).unwrap();
            top = store(node.get_type(), top);
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
        NodeKind::Var { .. } => {
            top = gen_addr(&node, top).unwrap();
            load(node.get_type(), top);
        }
        NodeKind::Unary(UnaryOp::Deref, child) => {
            top = gen_expr(child, top);
            load(node.get_type(), top);
        }
        NodeKind::Unary(UnaryOp::Addr, child) => {
            top = gen_addr(child, top).unwrap();
        }
        NodeKind::FunCall { name, args } => {
            let nargs = args.len();
            args.iter().for_each(|arg| top = gen_expr(arg, top));

            for i in 1..=nargs {
                top -= 1;
                println!("  mov {}, {}", reg(top), arg_reg64(nargs - i));
            }

            // 何故reg11もpushする必要がある?
            println!("  push %r10");
            println!("  push %r11");
            println!("  mov $0, %rax");
            println!("  call {}", name);
            println!("  pop %r11");
            println!("  pop %r10");
            println!("  mov %rax, {}", reg(top));
            top += 1;
        }
        _ => {
            error(&format!("invalid expression: {:?}", node));
        }
    }
    top
}

// return register top index
fn gen_stmt(
    node: &Node,
    label_counter: &mut LabelCounter,
    func: &Function,
    top: usize,
) -> Result<usize, String> {
    let stack_top = match &node.kind {
        NodeKind::Unary(UnaryOp::Return, child) => {
            let top = gen_expr(child, top) - 1;
            // Set the result of the expression to RAX so that
            // the result becomes a return value of this function.
            println!("  mov {}, %rax", reg(top));
            println!("  jmp .L.return.{}", func.name);

            Ok(top)
        }
        NodeKind::Unary(UnaryOp::ExprStmt, child) => Ok(gen_expr(child, top) - 1),
        NodeKind::If { cond, then, els } => {
            let c = label_counter.next().unwrap();
            let mut top = gen_expr(cond, top);
            println!("  cmp $0, {}", reg(top - 1));
            top -= 1;
            println!("  je .L.else.{}", c);
            top = gen_stmt(then, label_counter, func, top)?;
            println!("  jmp .L.end.{}", c);
            println!(".L.else.{}:", c);

            if let Some(node) = els.as_ref() {
                top = gen_stmt(node, label_counter, func, top)?;
            }
            println!(".L.end.{}:", c);
            Ok(top)
        }
        NodeKind::For {
            cond,
            then,
            init,
            inc,
        } => {
            let c = label_counter.next().unwrap();
            let mut top = gen_stmt(init, label_counter, func, top)?;
            println!(".L.begin.{}:", c);
            if let Some(node) = cond.as_ref() {
                top = gen_expr(node, top);
                println!("  cmp $0, {}", reg(top - 1));
                top -= 1;
                println!("  je .L.end.{}", c);
            }
            top = gen_stmt(then, label_counter, func, top)?;
            if let Some(node) = inc.as_ref() {
                top = gen_expr(node, top);
                top -= 1;
            }
            println!("  jmp .L.begin.{}", c);
            println!(".L.end.{}:", c);
            Ok(top)
        }
        NodeKind::While { cond, then } => {
            let c = label_counter.next().unwrap();
            println!(".L.begin.{}:", c);
            let mut top = gen_expr(cond, top);
            println!("  cmp $0, {}", reg(top - 1));
            top -= 1;
            println!("  je .L.end.{}", c);
            top = gen_stmt(then, label_counter, func, top)?;
            println!("  jmp .L.begin.{}", c);
            println!(".L.end.{}:", c);
            Ok(top)
        }
        NodeKind::Block(body) => body.iter().fold(Ok(top), |acc, node| {
            acc.and_then(|x| gen_stmt(&node, label_counter, func, top).and_then(|y| Ok(x + y)))
        }),
        _ => Err(format!("invalid statement: {:?}", node)),
    };
    match stack_top {
        Ok(0) => Ok(0),
        Ok(_) => Err(format!("statement register top is invalid: {:?}", node)),
        Err(msg) => Err(msg),
    }
}

fn emit_data(prog: &Program) {
    println!(".data");
    for var in prog.globals.iter() {
        println!("{}:", var.name);
        if let VarType::Global(Some(init_data)) = var.var_ty.clone() {
            for ch in init_data.chars() {
                let chnum = ch as u32;
                println!("  .byte {}", chnum);
            }
        } else {
            println!("  .zero {}", var.ty.size);
        }
    }
}

fn emit_text(prog: &Program) {
    println!(".text");

    let mut label_counter = LabelCounter::new();

    for func in prog.fns.iter() {
        println!(".globl {}", func.name);
        println!("{}:", func.name);

        // Prologue %r12-15 are callee-saved registers.
        println!("  push %rbp");
        println!("  mov %rsp, %rbp"); // 現在のrspをrbpにセット
        println!("  sub ${}, %rsp", func.stack_size); // 関数のスタックサイズ
        println!("  mov %r12, -8(%rbp)");
        println!("  mov %r13, -16(%rbp)");
        println!("  mov %r14, -24(%rbp)");
        println!("  mov %r15, -32(%rbp)");

        // Save arguments to the stack
        let nargs = func.params.len();
        for (i, param) in func.params.iter().enumerate() {
            if let VarType::Local(offset) = param.var_ty.clone() {
                match param.ty.kind.as_ref() {
                    TypeKind::Char => {
                        println!("  mov {}, -{}(%rbp)", arg_reg8(nargs - i - 1), offset.get());
                    }
                    _ => {
                        println!(
                            "  mov {}, -{}(%rbp)",
                            arg_reg64(nargs - i - 1),
                            offset.get()
                        );
                    }
                }
            }
        }

        // Emit code
        if let Err(msg) = gen_stmt(&func.body, &mut label_counter, &func, 0) {
            error(&msg);
        }

        // Epilogue
        println!(".L.return.{}:", func.name);
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
}

pub fn codegen(prog: Program) {
    emit_data(&prog);
    emit_text(&prog);
}
