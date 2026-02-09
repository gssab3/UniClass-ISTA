package it.unisa.uniclass.testing.benchmark.jmh.conversazioni;

import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.TopicService;
import it.unisa.uniclass.conversazioni.service.dao.TopicRemote;
import it.unisa.uniclass.orari.model.Corso;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;
import org.openjdk.jmh.results.format.ResultFormatType;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;
import org.mockito.MockedConstruction;

import javax.naming.InitialContext;
import java.lang.reflect.Field;
import java.util.Collections;
import java.util.concurrent.TimeUnit;

import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.mockConstruction;
import static org.mockito.Mockito.when;

@State(Scope.Benchmark)
public class benchmarkTopicService {

    private TopicService topicService;
    private Topic topicStatico;

    public static void main(String[] args) throws RunnerException {
        Options opt = new OptionsBuilder()
                .include(benchmarkTopicService.class.getSimpleName())

                // --- PARAMETRI DI STABILITÀ (Identici a MessaggioService) ---
                .forks(3)                   // 3 processi JVM
                .warmupIterations(10)       // 10 iterazioni warmup
                .measurementIterations(10)  // 10 iterazioni misura
                .mode(Mode.All)             // Misura Throughput, AvgTime, ecc.

                // --- CONFIGURAZIONE TEMPO ---
                // Limitiamo a 1 secondo per iterazione per non rendere il test infinito
                .warmupTime(org.openjdk.jmh.runner.options.TimeValue.seconds(1))
                .measurementTime(org.openjdk.jmh.runner.options.TimeValue.seconds(1))

                .timeUnit(TimeUnit.MICROSECONDS)
                .resultFormat(ResultFormatType.JSON)
                .result("jmh-result-topic.json") // File di output specifico per Topic

                // Ignora il lock file per evitare errori di avvio
                .jvmArgs("-Djmh.ignoreLock=true")
                .build();

        new Runner(opt).run();
    }

    @Setup(Level.Trial)
    public void setUp() throws Exception {
        // 1. Crea il Mock del DAO
        TopicRemote mockDao = mock(TopicRemote.class);

        // 2. Prepara l'oggetto statico complesso (Topic + Corso + CorsoLaurea)
        // Questo evita NullPointerException se il service accede ai sotto-oggetti
        CorsoLaurea corsoLaurea = new CorsoLaurea();
        corsoLaurea.setNome("Informatica");

        Corso corso = new Corso();
        corso.setNome("Programmazione Distribuita");
        corso.setCorsoLaurea(corsoLaurea);

        topicStatico = new Topic();
        topicStatico.setNome("Esame Finale");
        topicStatico.setCorsoLaurea(corsoLaurea);
        topicStatico.setCorso(corso);

        // 3. STUBBING PREVENTIVO (Configurazione Mockito)
        // Configuriamo tutte le possibili chiamate di lettura per restituire l'oggetto statico
        when(mockDao.trovaId(anyLong())).thenReturn(topicStatico);
        when(mockDao.trovaNome(anyString())).thenReturn(topicStatico);
        when(mockDao.trovaCorsoLaurea(anyString())).thenReturn(topicStatico);
        when(mockDao.trovaCorso(anyString())).thenReturn(topicStatico);
        when(mockDao.trovaTutti()).thenReturn(Collections.singletonList(topicStatico));
        // aggiungiTopic e rimuoviTopic sono void, non hanno bisogno di stubbing

        // 4. FIX JNDI (Il trucco per far funzionare il costruttore)
        // Simuliamo InitialContext solo durante la "new TopicService()"
        try (MockedConstruction<InitialContext> ctxMock = mockConstruction(InitialContext.class,
                (mock, context) -> {
                    // Quando il service chiede il DAO, gli diamo il mock
                    when(mock.lookup(any(String.class))).thenReturn(mockDao);
                })) {

            // Il costruttore ora troverà il mockDao e non crasherà
            topicService = new TopicService();
        }

        // 5. INIEZIONE VIA REFLECTION
        // Sovrascriviamo il campo privato per sicurezza
        injectDao(topicService, mockDao);
    }

    /**
     * Helper per iniettare il DAO corretto nel service
     */
    private void injectDao(Object targetService, Object daoImplementation) throws Exception {
        Field[] fields = targetService.getClass().getDeclaredFields();
        for (Field field : fields) {
            // Cerca il campo di tipo TopicRemote
            if (field.getType().equals(TopicRemote.class)) {
                field.setAccessible(true);
                field.set(targetService, daoImplementation);
                return;
            }
        }
        throw new RuntimeException("Impossibile trovare il campo TopicRemote nel service!");
    }

    // --- BENCHMARK METHODS ---

    @Benchmark
    public void trovaIdBenchmark(Blackhole bh) {
        bh.consume(topicService.trovaId(1L));
    }

    @Benchmark
    public void trovaNomeBenchmark(Blackhole bh) {
        bh.consume(topicService.trovaNome("Esame Finale"));
    }

    @Benchmark
    public void trovaCorsoLaureaBenchmark(Blackhole bh) {
        bh.consume(topicService.trovaCorsoLaurea("Informatica"));
    }

    @Benchmark
    public void trovaCorsoBenchmark(Blackhole bh) {
        bh.consume(topicService.trovaCorso("Programmazione Distribuita"));
    }

    @Benchmark
    public void trovaTuttiBenchmark(Blackhole bh) {
        bh.consume(topicService.trovaTutti());
    }

    @Benchmark
    public void aggiungiTopicBenchmark(Blackhole bh) {
        // Usiamo l'oggetto statico per non allocare memoria inutile
        topicService.aggiungiTopic(topicStatico);
        bh.consume(topicStatico);
    }

    @Benchmark
    public void rimuoviTopicBenchmark(Blackhole bh) {
        topicService.rimuoviTopic(topicStatico);
        bh.consume(topicStatico);
    }
}