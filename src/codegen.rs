use std::cell::RefCell;
use std::ops::Deref;
use std::rc::Rc;
use std::unimplemented;

use crate::parser::*;
use crate::types::{Type, TypeKind};
use crate::{
    node::{BinOp, Node, NodeKind, UnaryOp, VarType},
    util::LabelCounter,
};
use anyhow::anyhow;
use anyhow::Result;

const REGISTERS: [&str; 6] = ["%r10", "%r11", "%r12", "%r13", "%r14", "%r15"];
const ARG_REGISTERS8: [&str; 6] = ["%dil", "%sil", "%dl", "%cl", "%r8b", "%r9b"];
const ARG_REGISTERS16: [&str; 6] = ["%di", "%si", "%dx", "%cx", "%r8w", "%r9w"];
const ARG_REGISTERS32: [&str; 6] = ["%edi", "%esi", "%edx", "%ecx", "%r8d", "%r9d"];
const ARG_REGISTERS64: [&str; 6] = ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"];

fn reg_access(reg: [&'static str; 6], idx: usize) -> &'static str {
    reg.get(idx)
        .expect(&format!("register out of range: {}", idx))
}

fn reg(idx: usize) -> &'static str {
    reg_access(REGISTERS, idx)
}

fn arg_reg32(idx: usize) -> &'static str {
    reg_access(ARG_REGISTERS32, idx)
}

fn arg_reg64(idx: usize) -> &'static str {
    reg_access(ARG_REGISTERS64, idx)
}

fn get_arg_reg(idx: usize, size: usize) -> &'static str {
    match size {
        1 => reg_access(ARG_REGISTERS8, idx),
        2 => reg_access(ARG_REGISTERS16, idx),
        4 => reg_access(ARG_REGISTERS32, idx),
        8 => arg_reg64(idx),
        _ => unimplemented!("not implemented register bit size."),
    }
}

fn load(ty: Rc<RefCell<Type>>, top: usize) {
    let r = reg(top - 1);
    match ty.borrow().kind.as_ref() {
        TypeKind::Arr { .. } | TypeKind::Struct { .. } => {
            // If it is an array / struct, do nothing because in general we can't load
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
        TypeKind::Short => {
            println!("  movswq ({}), {}", r, r);
        }
        TypeKind::Int => {
            // 32bitオペランドを64bitに拡張してmove
            println!("  movsxd ({}), {}", r, r);
        }
        _ => {
            println!("  mov ({}), {}", r, r);
        }
    }
}

fn store(ty: Rc<RefCell<Type>>, top: usize) -> usize {
    let rd = reg(top - 1);
    let rs = reg(top - 2);
    match ty.borrow().kind.as_ref() {
        TypeKind::Struct { .. } => {
            for i in 0..ty.borrow().size {
                println!("  mov {}({}), %al", i, rs);
                println!("  mov %al, {}({})", i, rd);
            }
        }
        TypeKind::Char => {
            println!("  mov {}b, ({})", rs, rd);
        }
        TypeKind::Short => {
            println!("  mov {}w, ({})", rs, rd);
        }
        TypeKind::Int => {
            println!("  mov {}d, ({})", rs, rd);
        }
        _ => {
            println!("  mov {}, ({})", rs, rd);
        }
    }
    top - 1
}

fn emit_data(prog: &Program) {
    println!(".data");
    for var in prog.globals.iter() {
        println!("{}:", var.name);
        if let VarType::Global(init_data) = var.var_ty.clone() {
            if init_data.len() > 0 {
                for s in init_data.iter() {
                    println!("  .byte {}", s);
                }
            } else {
                println!("  .zero {}", var.ty.borrow().size);
            }
        }
    }
}
struct FuncGenerator<'a> {
    func: &'a Function,
    label_counter: &'a mut LabelCounter,
}

impl<'a> FuncGenerator<'a> {
    fn new(func: &'a Function, label_counter: &'a mut LabelCounter) -> Self {
        Self {
            func: func,
            label_counter,
        }
    }

    fn gen_addr(&mut self, node: &Node, top: usize) -> Result<usize> {
        match &node.kind {
            NodeKind::Var { var } => {
                match var.var_ty.clone() {
                    VarType::Local(offset) => {
                        println!("  lea -{}(%rbp), {}", offset.get(), reg(top));
                    }
                    VarType::Global(_) => {
                        println!("  mov ${}, {}", var.name, reg(top));
                    }
                }
                Ok(top + 1)
            }
            NodeKind::Unary(UnaryOp::Member(member), child) => {
                let top = self.gen_addr(child, top)?;
                println!("  add ${}, {}", member.offset.get(), reg(top - 1));
                Ok(top)
            }
            NodeKind::Unary(UnaryOp::Deref, child) => {
                let top = self.gen_expr(child, top);
                top
            }
            NodeKind::Bin {
                op: BinOp::Comma,
                lhs,
                rhs,
            } => {
                let mut top = self.gen_expr(lhs, top)?;
                top -= 1;
                self.gen_addr(rhs, top)
            }
            _ => {
                let msg = format!("NodeKind is Invalid: {:?}, expected Var", node);
                Err(anyhow!(msg))
            }
        }
    }

    #[allow(unused_must_use)]
    fn gen_expr(&mut self, node: &Node, mut top: usize) -> Result<usize> {
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
                if let TypeKind::Arr { .. } = node.get_type_ref().borrow().kind.as_ref() {
                    unimplemented!("array will not be assigned.")
                }
                top = self.gen_expr(&*rhs, top)?;
                top = self.gen_addr(&*lhs, top)?;
                top = store(node.get_type_ref(), top);
            }
            NodeKind::Bin {
                op: BinOp::Comma,
                lhs,
                rhs,
            } => {
                let mut top = self.gen_expr(lhs, top)?;
                top -= 1;
                return self.gen_expr(rhs, top);
            }
            NodeKind::Bin { op, lhs, rhs } => {
                top = self.gen_expr(&*lhs, top)?;
                top = self.gen_expr(&*rhs, top)?;
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
                    _ => {
                        let msg = "Invalid BinOp, probably Assign".to_string();
                        return Err(anyhow!(msg));
                    }
                }
            }
            NodeKind::Var { .. } | NodeKind::Unary(UnaryOp::Member(..), ..) => {
                top = self.gen_addr(&node, top)?;
                load(node.get_type_ref(), top);
            }
            NodeKind::Unary(UnaryOp::Deref, child) => {
                top = self.gen_expr(child, top)?;
                load(node.get_type_ref(), top);
            }
            NodeKind::Unary(UnaryOp::Addr, child) => {
                top = self.gen_addr(child, top)?;
            }
            NodeKind::Unary(UnaryOp::StmtExpr, child) => {
                if let NodeKind::Block(nodes) = &child.kind {
                    for node in nodes.iter() {
                        self.gen_stmt(node, top);
                    }
                    top += 1;
                }
            }
            NodeKind::FunCall { name, args } => {
                let nargs = args.len();

                // save caller-saved registers
                // NOTE なぜここでcaller-saved registerというものがでてくるのか不思議
                println!("  push %r10");
                println!("  push %r11");
                // FIXME if letしすぎ
                for i in 0..nargs {
                    let arg = args.get(i).unwrap();

                    if let VarType::Local(offset) = &arg.var_ty {
                        match arg.ty.borrow().kind.deref() {
                            TypeKind::Char => {
                                println!("  movsbl -{}(%rbp), {}", offset.get(), arg_reg32(i));
                            }
                            TypeKind::Short => {
                                println!("  movswl -{}(%rbp), {}", offset.get(), arg_reg32(i));
                            }
                            TypeKind::Int => {
                                println!("  mov -{}(%rbp), {}", offset.get(), arg_reg32(i));
                            }
                            TypeKind::Long | TypeKind::Ptr(_) => {
                                println!("  mov -{}(%rbp), {}", offset.get(), arg_reg64(i));
                            }
                            _ => unimplemented!(
                                "this type {:#?} is not implemented on FunCall.",
                                arg.ty
                            ),
                        }
                        if arg.ty.borrow().size == 1 {
                            println!("  movsbq -{}(%rbp), {}", offset.get(), arg_reg64(i));
                        } else {
                            // ダブルワードをクワッドワードに符号拡張して転送
                            println!("  movsxd -{}(%rbp), {}", offset.get(), arg_reg64(i));
                        }
                    }
                }

                println!("  mov $0, %rax");
                println!("  call {}", name);
                println!("  pop %r11");
                println!("  pop %r10");
                println!("  mov %rax, {}", reg(top));
                top += 1;
            }
            NodeKind::NullExpr => {
                top += 1;
            }
            _ => {
                return Err(anyhow!(format!("invalid expression: {:?}", node)));
            }
        }
        Ok(top)
    }

    // return register top index
    fn gen_stmt(&mut self, node: &Node, top: usize) -> Result<usize> {
        let stack_top = match &node.kind {
            NodeKind::Unary(UnaryOp::Return, child) => {
                let top = self.gen_expr(child, top)? - 1;
                // Set the result of the expression to RAX so that
                // the result becomes a return value of this function.
                println!("  mov {}, %rax", reg(top));
                println!("  jmp .L.return.{}", self.func.name);

                Ok(top)
            }
            NodeKind::Unary(UnaryOp::ExprStmt, child) => Ok(self.gen_expr(child, top)? - 1),
            NodeKind::If { cond, then, els } => {
                let c = self.label_counter.next().unwrap();
                let mut top = self.gen_expr(cond, top)?;
                println!("  cmp $0, {}", reg(top - 1));
                top -= 1;
                println!("  je .L.else.{}", c);
                top = self.gen_stmt(then, top)?;
                println!("  jmp .L.end.{}", c);
                println!(".L.else.{}:", c);

                if let Some(node) = els.as_ref() {
                    top = self.gen_stmt(node, top)?;
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
                let c = self.label_counter.next().unwrap();
                let mut top = self.gen_stmt(init, top)?;
                println!(".L.begin.{}:", c);
                if let Some(node) = cond.as_ref() {
                    top = self.gen_expr(node, top)?;
                    println!("  cmp $0, {}", reg(top - 1));
                    top -= 1;
                    println!("  je .L.end.{}", c);
                }
                top = self.gen_stmt(then, top)?;
                if let Some(node) = inc.as_ref() {
                    top = self.gen_expr(node, top)?;
                    top -= 1;
                }
                println!("  jmp .L.begin.{}", c);
                println!(".L.end.{}:", c);
                Ok(top)
            }
            NodeKind::While { cond, then } => {
                let c = self.label_counter.next().unwrap();
                println!(".L.begin.{}:", c);
                let mut top = self.gen_expr(cond, top)?;
                println!("  cmp $0, {}", reg(top - 1));
                top -= 1;
                println!("  je .L.end.{}", c);
                top = self.gen_stmt(then, top)?;
                println!("  jmp .L.begin.{}", c);
                println!(".L.end.{}:", c);
                Ok(top)
            }
            NodeKind::Block(body) => body.iter().fold(Ok(top), |acc, node| {
                acc.and_then(|x| self.gen_stmt(&node, top).and_then(|y| Ok(x + y)))
            }),
            _ => Err(anyhow!("invalid statement: {:?}", node)),
        };
        match stack_top {
            Ok(x) => Ok(x),
            Err(msg) => Err(msg),
        }
    }
}

fn emit_text(prog: &Program) -> Result<()> {
    println!(".text");

    let mut org_label_counter = LabelCounter::new();
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
                let r = get_arg_reg(nargs - i - 1, param.ty.borrow().size);
                println!("  mov {}, -{}(%rbp)", r, offset.get());
            }
        }

        let mut fn_gen = FuncGenerator::new(func, &mut org_label_counter);

        // Emit code
        if let Err(msg) = fn_gen.gen_stmt(&fn_gen.func.body, 0) {
            return Err(anyhow!(msg));
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
    Ok(())
}

pub fn codegen(prog: Program) -> Result<()> {
    emit_data(&prog);
    emit_text(&prog)?;
    Ok(())
}
