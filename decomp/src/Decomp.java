public class Decomp {
    // TODO
    static String parseHeader(String header) {
        return header;
    }

    static boolean checkSupportedLogic(String logic) {
        return false;
    }

    public static void main(String[] args) {
        String logic;

        if (args.length != 1) {
            System.out.println("USAGE: java Parser <file.tslmt>");
            System.exit(1);
        }

        logic = parseHeader(args[0]);
        if (!checkSupportedLogic(logic)) {
            System.out.printf("Unsupported logic: %s\n", logic);
            System.exit(1);
        }
    }
}
