import java.util.ArrayList;
import org.json.simple.JSONArray;
import org.json.simple.JSONObject;

public class Update {
    private String updateTerm;
    private String varName;
    private ArrayList<String> depends;

    public Update(String varName, String updateTerm) {
        this.updateTerm = updateTerm;
        this.varName = varName;
        depends = new ArrayList<String>();
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) return false;
        if (obj == this) return true;
        if (!(obj instanceof Update)) return false;
        boolean eqUpdateTerm = this.updateTerm.equals(((Update) obj).updateTerm);
        boolean eqVarName = this.varName.equals(((Update) obj).varName);
        return eqUpdateTerm && eqVarName;
    }

    @Override
    public int hashCode() {
        String id = String.format("%s%s", this.varName, this.updateTerm);
        return id.hashCode();
    }

    public JSONObject toJson() {
        JSONObject obj = new JSONObject();
        JSONArray dependArr = new JSONArray();

        obj.put("update_term", this.updateTerm.trim());
        obj.put("var_name", this.varName.trim());
        obj.put("depends", dependArr);
        return obj;
    }
}
