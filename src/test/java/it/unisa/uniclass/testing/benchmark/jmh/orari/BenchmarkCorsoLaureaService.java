package it.unisa.uniclass.testing.benchmark.jmh.orari;

import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.service.CorsoLaureaService;
import it.unisa.uniclass.orari.service.dao.CorsoLaureaRemote;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;
import org.openjdk.jmh.results.format.ResultFormatType;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;

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
public class BenchmarkCorsoLaureaService {

    private CorsoLaureaService service;
    private CorsoLaurea corsoLaureaStatico;

    public static void main(String[] args) throws RunnerException {
        Options opt = new OptionsBuilder()
                .include(BenchmarkCorsoLaureaService.class.getSimpleName())
                .resultFormat(ResultFormatType.JSON)
                .result("jmh-result-corso-laurea.json")
                .build();

        new Runner(opt).run();
    }

    @Setup(Level.Trial)
    public void setUp() {
        CorsoLaureaRemote mockDao = mock(CorsoLaureaRemote.class);

        corsoLaureaStatico = new CorsoLaurea();
        corsoLaureaStatico.setNome("Informatica");

        when(mockDao.trovaCorsoLaurea(anyLong())).thenReturn(corsoLaureaStatico);
        when(mockDao.trovaCorsoLaurea(anyString())).thenReturn(corsoLaureaStatico);
        when(mockDao.trovaTutti()).thenReturn(Collections.singletonList(corsoLaureaStatico));

        service = new CorsoLaureaService(mockDao);
    }

    @Benchmark
    public void trovaCorsoLaureaIdBenchmark(Blackhole bh) {
        bh.consume(service.trovaCorsoLaurea(1L));
    }

    @Benchmark
    public void trovaCorsoLaureaNomeBenchmark(Blackhole bh) {
        bh.consume(service.trovaCorsoLaurea("Informatica"));
    }

    @Benchmark
    public void trovaTuttiBenchmark(Blackhole bh) {
        bh.consume(service.trovaTutti());
    }

    @Benchmark
    public void aggiungiCorsoLaureaBenchmark(Blackhole bh) {
        service.aggiungiCorsoLaurea(corsoLaureaStatico);
        bh.consume(corsoLaureaStatico);
    }

    @Benchmark
    public void rimuoviCorsoLaureaBenchmark(Blackhole bh) {
        service.rimuoviCorsoLaurea(corsoLaureaStatico);
        bh.consume(corsoLaureaStatico);
    }
}

