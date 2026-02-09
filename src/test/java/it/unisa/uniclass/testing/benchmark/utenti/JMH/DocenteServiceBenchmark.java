package it.unisa.uniclass.testing.benchmark.utenti.JMH;

import it.unisa.uniclass.testing.benchmark.utenti.mocks.MockDocenteDAO;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.util.concurrent.TimeUnit;

@State(Scope.Thread)
@BenchmarkMode({Mode.Throughput, Mode.AverageTime, Mode.SampleTime, Mode.SingleShotTime})
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@Warmup(iterations = 10, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 10, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(3)
public class DocenteServiceBenchmark {

    private DocenteService docenteService;

    private static final String MATRICOLA = "005566";
    private static final String CORSO = "Informatica";

    @Setup(Level.Trial)
    public void setup() {
        MockDocenteDAO mockDao = new MockDocenteDAO();
        Docente d = new Docente();
        d.setMatricola(MATRICOLA);
        d.setNome("Luca");
        d.setCognome("Verdi");

        mockDao.setDocenteDaRitornare(d);
        this.docenteService = new DocenteService(mockDao);
    }

    @Benchmark
    public void benchmarkTrovaPerMatricola(Blackhole bh) {
        bh.consume(docenteService.trovaDocenteUniClass(MATRICOLA));
    }

    @Benchmark
    public void benchmarkTrovaPerCorso(Blackhole bh) {
        bh.consume(docenteService.trovaDocenteCorsoLaurea(CORSO));
    }

    @Benchmark
    public void benchmarkTrovaPerMatricolaFallito(Blackhole bh) {
        bh.consume(docenteService.trovaDocenteUniClass("000000"));
    }

    @Benchmark
    public void benchmarkTrovaPerCorsoFallito(Blackhole bh) {
        bh.consume(docenteService.trovaDocenteCorsoLaurea("Chimica"));
    }
}
