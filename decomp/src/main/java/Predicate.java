import java.util.HashSet;
import org.json.simple.JSONArray;
import org.json.simple.JSONObject;

public class Predicate {
    private String literal;
    private HashSet<String> temporal;

    public Predicate(String literal) {
        this.literal = literal;
        this.temporal = new HashSet<>();
    }

    public void addTemporal(String operator) {
        this.temporal.add(operator);
    }

    public JSONObject toJson() {
        JSONObject obj = new JSONObject();
        JSONArray temporalArray = new JSONArray();

        obj.put("pred", this.literal.trim());
        temporalArray.addAll(this.temporal);
        obj.put("temporal", temporalArray);

        return obj;
    }
}
