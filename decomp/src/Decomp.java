import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.text.ParseException;
import java.util.Scanner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.ArrayList;

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

    public static void main(String[] args)
            throws FileNotFoundException, IOException, ParseException {
        String path, logic;

//        if (args.length != 1) {
//            System.err.println("USAGE: java Parser <file.tslmt>");
//            System.exit(1);
//        }
        args = new String[]{"decomp", "cfs.tslmt"};
        path  = args[1];

        logic = getLogic(path);
        if (!checkSupportedLogic(logic)) {
            System.err.printf("Unsupported logic: %s\n", logic);
            System.exit(1);
        }
        ArrayList<Update> foo = Parser.getUpdates(path);
        for (Update u: foo)
            System.out.println(u.toJson());
    }
}
