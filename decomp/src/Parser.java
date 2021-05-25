import java.io.*;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Hashtable;
import java.util.HashSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;


public class Parser {
    private static final int FUNC_NAME_IDX = 1;
    private static final int ARITY_IDX = 2;
    private static final int PRED_IDX = 3;

    private static String removeAnsiColorCode(String input) {
        return input.replaceAll("\u001B\\[[;\\d]*m", "").trim();
    }

    public static Hashtable<String, Integer> getPredicateTerms(String path)
        throws java.io.IOException {
        String arg = String.format("../bin/tslsym %s", path);
        Hashtable<String, Integer> hashtable = new Hashtable<>();

        ProcessBuilder builder = new ProcessBuilder("bash", "-c", arg);
        builder.redirectErrorStream(true);
        Process p = builder.start();
        BufferedReader r = new BufferedReader(new InputStreamReader(p.getInputStream()));

        while (true) {
            String line, predicate;
            int arity;
            line = r.readLine();

            if (line == null) { break; }

            String [] columnEntries = Arrays.stream(line.split(";"))
                    .map(Parser::removeAnsiColorCode)
                    .toArray(String[]::new);
            if (columnEntries.length < PRED_IDX + 1) { continue; }

            if (!columnEntries[PRED_IDX].equals("predicate")) { continue; }

            predicate = columnEntries[FUNC_NAME_IDX];
            arity = columnEntries[ARITY_IDX].split("->").length - 1;
            hashtable.put(predicate, arity);
        }

        return hashtable;
    }

    public static ArrayList<Predicate> getPredicates(String path)
        throws java.io.IOException {
        Hashtable<String, Integer> predicateTerms = getPredicateTerms(path);

        ArrayList<Predicate> list = new ArrayList<>();
        Predicate testPred = new Predicate("eq loc 0");
        list.add(testPred);

        return list;
    }

    public static String fooTest(String path) throws IOException, ParseException {
        ArrayList<Update> foo = getUpdates(path);
        StringBuilder str = new StringBuilder();
        for (Update u: foo) {
            str.append(u.toJson()).append("\n");
        }
        return str.toString();
    }

    public static ArrayList<Update> getUpdates(String path)
            throws  java.io.IOException, ParseException {
        HashSet<Update> updateHashSet = new HashSet<>();
        BufferedReader reader = new BufferedReader(new FileReader(path));

        while (true) {
            String line;
            line = reader.readLine();
            if (line == null) { break; }
            Pattern pattern = Pattern.compile("\\[(.+?)\\]");
            Matcher matcher = pattern.matcher(line);
            while (matcher.find()) {
                String varName, updateTerm;
                String [] parsedUpdate = matcher.group(1).split("<-");

                if (parsedUpdate.length != 2) {
                    String errMsg = "Update term doesn't have exactly one <-\n" +
                            line;
                    throw new ParseException(errMsg, -1);
                }

                varName = parsedUpdate[0];
                updateTerm = parsedUpdate[1];
                Update newUpdate = new Update(varName, updateTerm);
                updateHashSet.add(newUpdate);
            }
        }

        return new ArrayList<>(updateHashSet);
    }
}
