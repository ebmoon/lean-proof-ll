use lean_proof_ll::{TypeParser, LeanType};
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    
    if args.len() < 2 {
        println!("Usage: {} <json_file_path>", args[0]);
        println!("Example: {} examples/prime_subgoals.json", args[0]);
        return;
    }

    let file_path = &args[1];
    
    match TypeParser::parse_json_file(file_path) {
        Ok(proof_data) => {
            println!("Successfully parsed {} proof steps from {}", proof_data.proof_steps.len(), file_path);
            println!();
            
            for (i, step) in proof_data.proof_steps.iter().enumerate() {
                println!("Goal {}:", i + 1);
                println!("  Hypotheses:");
                for hyp in &step.goals.hypotheses {
                    println!("    {} : {}", hyp.name.join(" "), format_lean_type(&hyp.ty));
                }
                println!("  Proposition: ⊢ {}", format_lean_type(&step.goals.proposition));
                println!();
            }
        }
        Err(e) => {
            eprintln!("Error parsing file: {}", e);
        }
    }

}

fn format_lean_type(ty: &LeanType) -> String {
    match ty {
        LeanType::Var(name) => name.clone(),
        LeanType::Arrow(left, right) => format!("{} → {}", format_lean_type(left), format_lean_type(right)),
        LeanType::Forall(var, var_ty, body) => format!("∀ ({} : {}), {}", var.join(" "), format_lean_type(var_ty), format_lean_type(body)),
        LeanType::Exists(var, var_ty, body) => format!("∃ ({} : {}), {}", var.join(" "), format_lean_type(var_ty), format_lean_type(body)),
        LeanType::App(func, arg) => format!("{} {}", format_lean_type(func), format_lean_type(arg)),
        LeanType::BinOp(op, left, right) => format!("{} {} {}", format_lean_type(left), op, format_lean_type(right)),
        LeanType::Not(inner) => format!("¬{}", format_lean_type(inner)),
        LeanType::Eq(left, right) => format!("{} = {}", format_lean_type(left), format_lean_type(right)),
        LeanType::And(left, right) => format!("{} ∧ {}", format_lean_type(left), format_lean_type(right)),
        LeanType::Or(left, right) => format!("{} ∨ {}", format_lean_type(left), format_lean_type(right)),
        LeanType::Implies(left, right) => format!("{} → {}", format_lean_type(left), format_lean_type(right)),
        LeanType::Divides(left, right) => format!("{} ∣ {}", format_lean_type(left), format_lean_type(right)),
        LeanType::Mod(left, right) => format!("{} % {}", format_lean_type(left), format_lean_type(right)),
        LeanType::Mul(left, right) => format!("{} * {}", format_lean_type(left), format_lean_type(right)),
        LeanType::Lt(left, right) => format!("{} < {}", format_lean_type(left), format_lean_type(right)),
        LeanType::Ne(left, right) => format!("{} ≠ {}", format_lean_type(left), format_lean_type(right)),
        LeanType::False => "False".to_string(),
        LeanType::True => "True".to_string(),
    }
}
