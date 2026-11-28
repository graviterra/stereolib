import java.nio.file.Files;
import java.nio.file.Paths;
import com.simolecule.centres.config.Tetrahedral;

/** Read one explicitly framed, root-zero graph; compare native and both metrics. */
public final class CentresPublishedMetric {
  static CentresProbe read(java.nio.file.Path file) throws Exception {
    CentresProbe molecule = new CentresProbe(file.getFileName().toString());
    for (String line : Files.readAllLines(file)) {
      String[] fields = line.split(" ");
      switch (fields[0]) {
        case "a":
          molecule.elements.add(Integer.parseInt(fields[1]));
          break;
        case "b":
          molecule.edges.add(new int[] {
              Integer.parseInt(fields[1]), Integer.parseInt(fields[2])});
          break;
        case "f":
          molecule.frames.add(new int[] {
              Integer.parseInt(fields[1]),
              switch (fields[2]) { case "R" -> Tetrahedral.RIGHT; case "S" -> Tetrahedral.LEFT;
                default -> throw new IllegalArgumentException(line); },
              Integer.parseInt(fields[3]), Integer.parseInt(fields[4]),
              Integer.parseInt(fields[5]), Integer.parseInt(fields[6])});
          break;
        default:
          throw new IllegalArgumentException(line);
      }
    }
    return molecule;
  }

  public static void main(String[] args) throws Exception {
    CentresProbe molecule = read(Paths.get(args[0]));
    String nativeLabel = CentresOxaziridineRoot.run(molecule, 0);
    String control = CentresAuxiliaryDistance.run(
        molecule, false, new CentresAuxiliaryDistance.Measurements(false));
    CentresAuxiliaryDistance.Measurements measured =
        new CentresAuxiliaryDistance.Measurements(false);
    String active = CentresAuxiliaryDistance.run(molecule, true, measured);
    System.out.println(nativeLabel + " " + control + " " + active + " "
        + measured.comparisons + " " + measured.reversals);
  }
}
