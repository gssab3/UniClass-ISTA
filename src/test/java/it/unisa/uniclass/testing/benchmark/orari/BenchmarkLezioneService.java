package it.unisa.uniclass.testing.benchmark.orari;

import it.unisa.uniclass.orari.model.*;
import it.unisa.uniclass.orari.service.LezioneService;
import it.unisa.uniclass.orari.service.dao.LezioneRemote;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;
import org.openjdk.jmh.results.format.ResultFormatType;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;

import java.sql.Time;
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
public class BenchmarkLezioneService {

    private LezioneService service;
    private Lezione lezioneStatica;
    private Time oraInizio;
    private Time oraFine;

    public static void main(String[] args) throws RunnerException {
        Options opt = new OptionsBuilder()
                .include(BenchmarkLezioneService.class.getSimpleName())
                .resultFormat(ResultFormatType.JSON)
                .result("jmh-result-lezione.json")
                .build();

        new Runner(opt).run();
    }

    @Setup(Level.Trial)
    public void setUp() {
        LezioneRemote mockDao = mock(LezioneRemote.class);

        oraInizio = Time.valueOf("09:00:00");
        oraFine = Time.valueOf("11:00:00");

        CorsoLaurea corsoLaurea = new CorsoLaurea();
        corsoLaurea.setNome("Informatica");

        Corso corso = new Corso();
        corso.setNome("Programmazione");
        corso.setCorsoLaurea(corsoLaurea);

        Aula aula = new Aula();
        aula.setNome("F3");
        aula.setEdificio("Stecca");

        lezioneStatica = new Lezione();
        lezioneStatica.setCorso(corso);
        lezioneStatica.setAula(aula);
        lezioneStatica.setOraInizio(oraInizio);
        lezioneStatica.setOraFine(oraFine);
        lezioneStatica.setGiorno(Giorno.LUNEDI);

        when(mockDao.trovaLezione(anyLong())).thenReturn(lezioneStatica);
        when(mockDao.trovaLezioniCorso(anyString())).thenReturn(Collections.singletonList(lezioneStatica));
        when(mockDao.trovaLezioniOre(any(Time.class), any(Time.class))).thenReturn(Collections.singletonList(lezioneStatica));
        when(mockDao.trovaLezioniOreGiorno(any(Time.class), any(Time.class), any(Giorno.class))).thenReturn(Collections.singletonList(lezioneStatica));
        when(mockDao.trovaLezioniAule(anyString())).thenReturn(Collections.singletonList(lezioneStatica));
        when(mockDao.trovaTutte()).thenReturn(Collections.singletonList(lezioneStatica));
        when(mockDao.trovaLezioniCorsoLaureaRestoAnno(anyLong(), anyLong(), anyInt())).thenReturn(Collections.singletonList(lezioneStatica));
        when(mockDao.trovaLezioniCorsoLaureaRestoAnnoSemestre(anyLong(), anyLong(), anyInt(), anyInt())).thenReturn(Collections.singletonList(lezioneStatica));
        when(mockDao.trovaLezioniDocente(anyString())).thenReturn(Collections.singletonList(lezioneStatica));

        service = new LezioneService(mockDao);
    }

    @Benchmark
    public void trovaLezioneIdBenchmark(Blackhole bh) {
        bh.consume(service.trovaLezione(1L));
    }

    @Benchmark
    public void trovaLezioniCorsoBenchmark(Blackhole bh) {
        bh.consume(service.trovaLezioniCorso("Programmazione"));
    }

    @Benchmark
    public void trovaLezioniOreBenchmark(Blackhole bh) {
        bh.consume(service.trovaLezioniOre(oraInizio, oraFine));
    }

    @Benchmark
    public void trovaLezioniOreGiornoBenchmark(Blackhole bh) {
        bh.consume(service.trovaLezioniOreGiorno(oraInizio, oraFine, Giorno.LUNEDI));
    }

    @Benchmark
    public void trovaLezioniAuleBenchmark(Blackhole bh) {
        bh.consume(service.trovaLezioniAule("F3"));
    }

    @Benchmark
    public void trovaTutteBenchmark(Blackhole bh) {
        bh.consume(service.trovaTutte());
    }

    @Benchmark
    public void trovaLezioniCorsoLaureaRestoAnnoBenchmark(Blackhole bh) {
        bh.consume(service.trovaLezioniCorsoLaureaRestoAnno(1L, 1L, 1));
    }

    @Benchmark
    public void trovaLezioniCorsoLaureaRestoAnnoSemestreBenchmark(Blackhole bh) {
        bh.consume(service.trovaLezioniCorsoLaureaRestoAnnoSemestre(1L, 1L, 1, 1));
    }

    @Benchmark
    public void trovaLezioniDocenteBenchmark(Blackhole bh) {
        bh.consume(service.trovaLezioniDocente("Mario Rossi"));
    }

    @Benchmark
    public void aggiungiLezioneBenchmark(Blackhole bh) {
        service.aggiungiLezione(lezioneStatica);
        bh.consume(lezioneStatica);
    }

    @Benchmark
    public void rimuoviLezioneBenchmark(Blackhole bh) {
        service.rimuoviLezione(lezioneStatica);
        bh.consume(lezioneStatica);
    }
}

