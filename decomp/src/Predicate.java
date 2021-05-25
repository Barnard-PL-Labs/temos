import java.util.ArrayList;

public class Predicate {
    private String pred;
    private ArrayList<String> temporal;

    public Predicate(String pred) {
        this.pred = pred;
        this.temporal = new ArrayList<String>();
    }

    public void addTemporal(String operator) {
        this.temporal.add(operator);
    }

    public String toJson(boolean test) {
        return "";
    }
}
