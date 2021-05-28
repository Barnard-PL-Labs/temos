import java.io.*;
import java.text.ParseException;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Parser {
    private static final int FUNC_NAME_IDX = 1;
    private static final int ARITY_IDX = 2;
    private static final int PRED_IDX = 3;
    private static final HashSet<String> LIA_OPS = new HashSet<>(Arrays.asList("eq",
            "gt", "gte", "lt", "lte"));

    private static String removeAnsiColorCode(String input) {
        return input.replaceAll("\u001B\\[[;\\d]*m", "").trim();
    }

    private static Hashtable<String, Integer> getPredArityDict(String path)
        throws java.io.IOException {
        String arg = String.format("bin/tslsym %s", path);
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
            if (!LIA_OPS.contains(predicate)) { continue; }

            arity = columnEntries[ARITY_IDX].split("->").length - 1;
            hashtable.put(predicate, arity);
        }

        if (p.exitValue() != 0) {
            System.err.println("Shell error!");
            System.exit(1);
        }

        return hashtable;
    }

    public static ArrayList<Predicate> getPredicates(String path)
            throws java.io.IOException, ParseException {
        Hashtable<String, Integer> predArityDict = getPredArityDict(path);
        HashMap<String, Predicate> predicates = new HashMap<>();
        ArrayList<Predicate> result = new ArrayList<>();
        Scanner scanner = new Scanner(new File(path));

        scanner.useDelimiter("\n");

        while (scanner.hasNext()) {
            ArrayList<String> wordsList = new ArrayList<>();

            for (String word : scanner.next().split(" ")) {
                if (Utils.isConstNullaryNumber(word))
                    word = String.valueOf(Utils.parseIntFromNullaryFunction(word));
                word = word.replaceAll("[^a-zA-Z0-9]+","");
                wordsList.add(word);
            }
            // Just easier for legacy code...
            String [] words = wordsList.toArray(new String[0]);

            // XXX
            for (int i = 0; i < words.length; i++) {
                String word = words[i];

                if (predArityDict.containsKey(word)) {
                    Predicate pred;
                    int arity = predArityDict.get(word);

                    String predLiteral = String.join(" ",
                            Arrays.copyOfRange(words, i, i + arity + 1));

                    if (!predicates.containsKey(predLiteral))
                        predicates.put(predLiteral, new Predicate(predLiteral));

                    pred = predicates.get(word);

                    if (0 < i && (words[i-1].equals("F") || words[i-1].equals("X")))
                        pred.addTemporal(words[i-1]);
                }
            }
        }

        // XXX
        for (Predicate pred : predicates.values()) {
            pred.addTemporal("X");
            pred.addTemporal("F");
            result.add(pred);
        }
        return result;
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
                String varName;
                StringBuilder updateTerm = new StringBuilder();
                String [] parsedUpdate = matcher.group(1).split("<-");

                if (parsedUpdate.length != 2) {
                    String errMsg = "Update term doesn't have exactly one <-\n" +
                            line;
                    throw new ParseException(errMsg, -1);
                }

                varName = parsedUpdate[0];
                for (String literal: parsedUpdate[1].split(" ")) {
                    if (Utils.isConstNullaryNumber(literal))
                        literal = String.valueOf(Utils.parseIntFromNullaryFunction(literal));
                    updateTerm.append(" ");
                    updateTerm.append(literal);
                }
                Update newUpdate = new Update(varName, updateTerm.toString());
                updateHashSet.add(newUpdate);
            }
        }

        return new ArrayList<>(updateHashSet);
    }
}
