package it.unisa.uniclass.testing.benchmark.orari;

import it.unisa.uniclass.orari.model.Aula;
import it.unisa.uniclass.orari.service.AulaService;
import it.unisa.uniclass.orari.service.dao.AulaRemote;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;
import org.openjdk.jmh.results.format.ResultFormatType;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;

import java.util.Arrays;
import java.util.Collections;
import java.util.concurrent.TimeUnit;

import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

@BenchmarkMode(Mode.All)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(2)
@State(Scope.Benchmark)
public class BenchmarkAulaService {

    private AulaService service;
    private Aula aulaStatica;

    public static void main(String[] args) throws RunnerException {
        Options opt = new OptionsBuilder()
                .include(BenchmarkAulaService.class.getSimpleName())
                .resultFormat(ResultFormatType.JSON)
                .result("jmh-result-aula.json")
                .build();

        new Runner(opt).run();
    }

    @Setup(Level.Trial)
    public void setUp() {
        AulaRemote mockDao = mock(AulaRemote.class);

        aulaStatica = new Aula();
        aulaStatica.setNome("F3");
        aulaStatica.setEdificio("Stecca");

        when(mockDao.trovaAula(anyInt())).thenReturn(aulaStatica);
        when(mockDao.trovaAula(anyString())).thenReturn(aulaStatica);
        when(mockDao.trovaTutte()).thenReturn(Collections.singletonList(aulaStatica));
        when(mockDao.trovaAuleEdificio(anyString())).thenReturn(Collections.singletonList(aulaStatica));
        when(mockDao.trovaEdifici()).thenReturn(Arrays.asList("Stecca", "F1"));

        service = new AulaService(mockDao);
    }

    @Benchmark
    public void trovaAulaIdBenchmark(Blackhole bh) {
        bh.consume(service.trovaAula(1));
    }

    @Benchmark
    public void trovaAulaNomeBenchmark(Blackhole bh) {
        bh.consume(service.trovaAula("F3"));
    }

    @Benchmark
    public void trovaTutteBenchmark(Blackhole bh) {
        bh.consume(service.trovaTutte());
    }

    @Benchmark
    public void trovaAuleEdificioBenchmark(Blackhole bh) {
        bh.consume(service.trovaAuleEdificio("Stecca"));
    }

    @Benchmark
    public void trovaEdificiBenchmark(Blackhole bh) {
        bh.consume(service.trovaEdifici());
    }

    @Benchmark
    public void aggiungiAulaBenchmark(Blackhole bh) {
        service.aggiungiAula(aulaStatica);
        bh.consume(aulaStatica);
    }

    @Benchmark
    public void rimuoviAulaBenchmark(Blackhole bh) {
        service.rimuoviAula(aulaStatica);
        bh.consume(aulaStatica);
    }
}

