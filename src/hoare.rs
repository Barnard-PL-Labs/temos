use crate::types::*;
use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;

// TODO: clean up w.r.t. to references...

fn var_updates(update_vec: Vec<Update>) 
    -> HashMap<String, HashSet<UpdateTerm>>  {

    let mut var_updates = HashMap::new();
    for update in &update_vec { 
        let var_vec = var_updates.entry(update.var_name.to_string())
                                 .or_insert(HashSet::new());
        var_vec.insert(update.update_term.clone());
    }
    var_updates
}

// O(n^3) but it's probably fast enough.
pub fn enumerate_hoare(pred_vec: Vec<SpecPredicate>,
                       update_vec: Vec<Update>) -> Vec<SygusHoareTriple> {

    let var_updates = var_updates(update_vec);
    let mut hoare_vec : Vec<SygusHoareTriple> = Vec::new();
    for precond in &pred_vec {
        let var_name = &precond.pred.get_var_name();
        if var_name.parse::<f64>().is_ok() {
            continue; //TEMP HACK
        }
        for postcond in &pred_vec {
            if &postcond.pred.get_var_name() != var_name {
                continue;
            }
            for operator in &postcond.temporal {
                let hoare = SygusHoareTriple {
                    precond : Rc::new(precond.pred.clone()),
                    postcond: Rc::new(postcond.pred.clone()),
                    var_name: var_name.to_string(),
                    temporal: Rc::new(operator.clone()),
                    updates : Rc::new(var_updates.get(var_name).unwrap().clone())
                };
                hoare_vec.push(hoare);
            }
        }
    } 
    hoare_vec 
}
