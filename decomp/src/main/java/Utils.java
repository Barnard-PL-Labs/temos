import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.text.ParseException;

public class Utils {

    public static boolean isConstNullaryNumber(String signal) {
        Pattern pattern = Pattern.compile("c[0-9]+\\(\\)");
        Matcher matcher = pattern.matcher(signal);
        return matcher.find();
    }

    public static int parseIntFromNullaryFunction(String signal)
            throws ParseException {
        String regexResult;
        Pattern pattern = Pattern.compile("c([0-9]+)\\(\\)");
        Matcher matcher = pattern.matcher(signal);

        if (!matcher.find()) {
             throw new ParseException("Please check argument.\n", -1);
        }
        regexResult = matcher.group(1);
        return Integer.parseInt(regexResult);
    }
}
