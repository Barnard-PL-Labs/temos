import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.text.ParseException;
import java.util.Arrays;
import java.util.Scanner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import org.json.simple.JSONArray;
import org.json.simple.JSONObject;

public class Decomp {
    // https://stackoverflow.com/a/3403112/11801882
    static String getLogic(String path) throws FileNotFoundException {
        String content = new Scanner(new File(path)).useDelimiter("\n").next();
        Pattern pattern = Pattern.compile("#(.*)#");
        Matcher matcher = pattern.matcher(content);
        if (!matcher.find()){
            System.err.printf("No logic header detected for: %s\n", content);
            System.exit(1);
        }
        return matcher.group(1);
    }

    static boolean checkSupportedLogic(String logic) {
        return logic.equals("LIA");
    }

    static JSONObject toJson(ArrayList<Predicate> predicates,
                             ArrayList<Update> updates) {
        List<JSONObject> predJsonList;
        List<JSONObject> updJsonList;
        JSONObject obj = new JSONObject();
        JSONArray predArr = new JSONArray();
        JSONArray updArr = new JSONArray();

        predJsonList = predicates.stream().map(Predicate::toJson).collect(Collectors.toList());
        updJsonList = updates.stream().map(Update::toJson).collect(Collectors.toList());

        predArr.addAll(predJsonList);
        updArr.addAll(updJsonList);

        obj.put("predicates", predArr);
        obj.put("updates", updArr);
        return obj;
    }

    public static void main(String[] args)
            throws IOException, ParseException {
        String path, logic;
        ArrayList<Predicate> predicates;
        ArrayList<Update> updates;

        if (args.length != 1) {
            System.err.println("USAGE: java Parser <file.tslmt>");
            System.exit(1);
        }

        path  = args[0];

        logic = getLogic(path);
        if (!checkSupportedLogic(logic)) {
            System.err.printf("Unsupported logic: %s\n", logic);
            System.exit(1);
        }
        predicates = Parser.getPredicates(path);
        updates = Parser.getUpdates(path);
        System.out.println(toJson(predicates, updates));
    }
}
