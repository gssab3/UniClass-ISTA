package it.unisa.uniclass.testing.unit.orari.model;

import it.unisa.uniclass.orari.model.AnnoDidattico;
import it.unisa.uniclass.orari.model.Corso;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.model.Lezione;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Nested;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test d'unità completi per la classe Corso.
 * Verifica costruttori, getter, setter, relazioni JPA e metodi di utilità.
 */
@DisplayName("Test per la classe Corso")
public class CorsoTest {

    private Corso corso;

    @BeforeEach
    void setUp() {
        corso = new Corso();
    }

    @Nested
    @DisplayName("Test dei Costruttori")
    class CostruttoriTest {

        @Test
        @DisplayName("Costruttore di default crea un'istanza valida")
        void testCostruttoreDefault() {
            Corso corsoTest = new Corso();
            assertNotNull(corsoTest);
            assertNull(corsoTest.getNome());
            assertNull(corsoTest.getCorsoLaurea());
            assertNull(corsoTest.getAnnoDidattico());
            assertNotNull(corsoTest.getLezioni());
            assertNotNull(corsoTest.getDocenti());
            assertTrue(corsoTest.getLezioni().isEmpty());
            assertTrue(corsoTest.getDocenti().isEmpty());
        }

        @Test
        @DisplayName("Costruttore con nome inizializza correttamente")
        void testCostruttoreConNome() {
            String nomeCors = "Ingegneria del Software";
            Corso corsoTest = new Corso(nomeCors);

            assertNotNull(corsoTest);
            assertEquals(nomeCors, corsoTest.getNome());
            assertNotNull(corsoTest.getLezioni());
            assertNotNull(corsoTest.getDocenti());
            assertTrue(corsoTest.getLezioni().isEmpty());
            assertTrue(corsoTest.getDocenti().isEmpty());
        }

        @Test
        @DisplayName("Costruttore con nome null")
        void testCostruttoreConNomeNull() {
            Corso corsoTest = new Corso(null);

            assertNotNull(corsoTest);
            assertNull(corsoTest.getNome());
            assertNotNull(corsoTest.getLezioni());
            assertNotNull(corsoTest.getDocenti());
        }

        @Test
        @DisplayName("Costruttore con nome vuoto")
        void testCostruttoreConNomeVuoto() {
            Corso corsoTest = new Corso("");

            assertNotNull(corsoTest);
            assertEquals("", corsoTest.getNome());
        }

        @Test
        @DisplayName("Costruttore con nome contenente spazi")
        void testCostruttoreConNomeSpazi() {
            String nomeCors = "Programmazione I - Parte A";
            Corso corsoTest = new Corso(nomeCors);

            assertNotNull(corsoTest);
            assertEquals(nomeCors, corsoTest.getNome());
        }
    }

    @Nested
    @DisplayName("Test dei Getter e Setter per 'nome'")
    class NomeGetterSetterTest {

        @Test
        @DisplayName("getNome restituisce null per default")
        void testGetNomeDefault() {
            assertNull(corso.getNome());
        }

        @Test
        @DisplayName("setNome e getNome funzionano correttamente")
        void testSetGetNome() {
            String nomeCors = "Algoritmi e Strutture Dati";
            corso.setNome(nomeCors);

            assertEquals(nomeCors, corso.getNome());
        }

        @Test
        @DisplayName("setNome con null è permesso")
        void testSetNomeNull() {
            corso.setNome("Programmazione");
            corso.setNome(null);

            assertNull(corso.getNome());
        }

        @Test
        @DisplayName("setNome con stringa vuota")
        void testSetNomeStringaVuota() {
            corso.setNome("");

            assertEquals("", corso.getNome());
        }

        @Test
        @DisplayName("Modifica sequenziale del nome")
        void testModificaSequenzialaNome() {
            corso.setNome("Corso A");
            assertEquals("Corso A", corso.getNome());

            corso.setNome("Corso B");
            assertEquals("Corso B", corso.getNome());

            corso.setNome("Corso C");
            assertEquals("Corso C", corso.getNome());
        }
    }

    @Nested
    @DisplayName("Test dei Getter e Setter per 'corsoLaurea'")
    class CorsoLaureaGetterSetterTest {

        @Test
        @DisplayName("getCorsoLaurea restituisce null per default")
        void testGetCorsoLaureaDefault() {
            assertNull(corso.getCorsoLaurea());
        }

        @Test
        @DisplayName("setCorsoLaurea e getCorsoLaurea funzionano correttamente")
        void testSetGetCorsoLaurea() {
            CorsoLaurea corsoLaurea = new CorsoLaurea();
            corso.setCorsoLaurea(corsoLaurea);

            assertEquals(corsoLaurea, corso.getCorsoLaurea());
        }

        @Test
        @DisplayName("setCorsoLaurea con null è permesso")
        void testSetCorsoLaureaNull() {
            CorsoLaurea corsoLaurea = new CorsoLaurea();
            corso.setCorsoLaurea(corsoLaurea);
            corso.setCorsoLaurea(null);

            assertNull(corso.getCorsoLaurea());
        }

        @Test
        @DisplayName("Modifica sequenziale del corso di laurea")
        void testModificaSequenzialeCorsoLaurea() {
            CorsoLaurea cl1 = new CorsoLaurea();
            CorsoLaurea cl2 = new CorsoLaurea();
            CorsoLaurea cl3 = new CorsoLaurea();

            corso.setCorsoLaurea(cl1);
            assertEquals(cl1, corso.getCorsoLaurea());

            corso.setCorsoLaurea(cl2);
            assertEquals(cl2, corso.getCorsoLaurea());

            corso.setCorsoLaurea(cl3);
            assertEquals(cl3, corso.getCorsoLaurea());
        }
    }

    @Nested
    @DisplayName("Test dei Getter e Setter per 'annoDidattico'")
    class AnnoDidatticoGetterSetterTest {

        @Test
        @DisplayName("getAnnoDidattico restituisce null per default")
        void testGetAnnoDidatticoDefault() {
            assertNull(corso.getAnnoDidattico());
        }

        @Test
        @DisplayName("setAnnoDidattico e getAnnoDidattico funzionano correttamente")
        void testSetGetAnnoDidattico() {
            AnnoDidattico anno = new AnnoDidattico();
            corso.setAnnoDidattico(anno);

            assertEquals(anno, corso.getAnnoDidattico());
        }

        @Test
        @DisplayName("setAnnoDidattico con null è permesso")
        void testSetAnnoDidatticoNull() {
            AnnoDidattico anno = new AnnoDidattico();
            corso.setAnnoDidattico(anno);
            corso.setAnnoDidattico(null);

            assertNull(corso.getAnnoDidattico());
        }

        @Test
        @DisplayName("Modifica sequenziale dell'anno didattico")
        void testModificaSequenzialeAnnoDidattico() {
            AnnoDidattico anno1 = new AnnoDidattico();
            AnnoDidattico anno2 = new AnnoDidattico();

            corso.setAnnoDidattico(anno1);
            assertEquals(anno1, corso.getAnnoDidattico());

            corso.setAnnoDidattico(anno2);
            assertEquals(anno2, corso.getAnnoDidattico());
        }
    }

    @Nested
    @DisplayName("Test del Getter per 'id'")
    class IdGetterTest {

        @Test
        @DisplayName("getId restituisce null per default")
        void testGetIdDefault() {
            assertNull(corso.getId());
        }

        @Test
        @DisplayName("getId restituisce il valore corretto dopo costruzione")
        void testGetIdConCostruttore() {
            Corso corsoTest = new Corso("Test");

            assertNull(corsoTest.getId());
        }
    }

    @Nested
    @DisplayName("Test dei Getter e Setter per 'lezioni'")
    class LezioniGetterSetterTest {

        @Test
        @DisplayName("getLezioni restituisce lista non null per default")
        void testGetLezioniDefault() {
            List<Lezione> lezioni = corso.getLezioni();

            assertNotNull(lezioni);
            assertTrue(lezioni.isEmpty());
        }

        @Test
        @DisplayName("setLezioni e getLezioni funzionano correttamente")
        void testSetGetLezioni() {
            List<Lezione> lezioniNuove = new ArrayList<>();
            lezioniNuove.add(new Lezione());
            lezioniNuove.add(new Lezione());

            corso.setLezioni(lezioniNuove);

            assertEquals(lezioniNuove, corso.getLezioni());
            assertEquals(2, corso.getLezioni().size());
        }

        @Test
        @DisplayName("Modifica della lista restituita da getLezioni si riflette sull'oggetto")
        void testModificaListaLezioni() {
            List<Lezione> lezioni = corso.getLezioni();
            Lezione nuovaLezione = new Lezione();
            lezioni.add(nuovaLezione);

            assertEquals(1, corso.getLezioni().size());
            assertTrue(corso.getLezioni().contains(nuovaLezione));
        }

        @Test
        @DisplayName("Aggiunta multipla di lezioni")
        void testAggiuntaMultiplaLezioni() {
            List<Lezione> lezioni = corso.getLezioni();
            for (int i = 0; i < 5; i++) {
                lezioni.add(new Lezione());
            }

            assertEquals(5, corso.getLezioni().size());
        }

        @Test
        @DisplayName("Rimozione di lezioni dalla lista")
        void testRimozioneLezoni() {
            List<Lezione> lezioni = corso.getLezioni();
            Lezione lez1 = new Lezione();
            Lezione lez2 = new Lezione();
            lezioni.add(lez1);
            lezioni.add(lez2);

            assertEquals(2, corso.getLezioni().size());

            lezioni.remove(lez1);

            assertEquals(1, corso.getLezioni().size());
            assertTrue(corso.getLezioni().contains(lez2));
            assertFalse(corso.getLezioni().contains(lez1));
        }

        @Test
        @DisplayName("setLezioni con null")
        void testSetLezioniNull() {
            corso.setLezioni(null);

            assertNull(corso.getLezioni());
        }
    }

    @Nested
    @DisplayName("Test dei Getter e Setter per 'docenti'")
    class DocentiGetterSetterTest {

        @Test
        @DisplayName("getDocenti restituisce lista non null per default")
        void testGetDocentiDefault() {
            List<Docente> docenti = corso.getDocenti();

            assertNotNull(docenti);
            assertTrue(docenti.isEmpty());
        }

        @Test
        @DisplayName("setDocenti e getDocenti funzionano correttamente")
        void testSetGetDocenti() {
            List<Docente> docentiNuovi = new ArrayList<>();
            docentiNuovi.add(new Docente());
            docentiNuovi.add(new Docente());

            corso.setDocenti(docentiNuovi);

            assertEquals(docentiNuovi, corso.getDocenti());
            assertEquals(2, corso.getDocenti().size());
        }

        @Test
        @DisplayName("Modifica della lista restituita da getDocenti si riflette sull'oggetto")
        void testModificaListaDocenti() {
            List<Docente> docenti = corso.getDocenti();
            Docente nuovoDocente = new Docente();
            docenti.add(nuovoDocente);

            assertEquals(1, corso.getDocenti().size());
            assertTrue(corso.getDocenti().contains(nuovoDocente));
        }

        @Test
        @DisplayName("Aggiunta multipla di docenti")
        void testAggiuntaMultiplaDocenti() {
            List<Docente> docenti = corso.getDocenti();
            for (int i = 0; i < 3; i++) {
                docenti.add(new Docente());
            }

            assertEquals(3, corso.getDocenti().size());
        }

        @Test
        @DisplayName("Rimozione di docenti dalla lista")
        void testRimozionDocenti() {
            List<Docente> docenti = corso.getDocenti();
            Docente doc1 = new Docente();
            Docente doc2 = new Docente();
            docenti.add(doc1);
            docenti.add(doc2);

            assertEquals(2, corso.getDocenti().size());

            docenti.remove(doc1);

            assertEquals(1, corso.getDocenti().size());
            assertTrue(corso.getDocenti().contains(doc2));
            assertFalse(corso.getDocenti().contains(doc1));
        }

        @Test
        @DisplayName("setDocenti con null")
        void testSetDocentiNull() {
            corso.setDocenti(null);

            assertNull(corso.getDocenti());
        }
    }

    @Nested
    @DisplayName("Test del metodo toString")
    class ToStringTest {

        @Test
        @DisplayName("toString con valori di default")
        void testToStringDefault() {
            String result = corso.toString();

            assertNotNull(result);
            assertTrue(result.contains("Corso"));
            assertTrue(result.contains("id="));
            assertTrue(result.contains("nome="));
        }

        @Test
        @DisplayName("toString con nome impostato")
        void testToStringConNome() {
            corso.setNome("Ingegneria del Software");
            String result = corso.toString();

            assertNotNull(result);
            assertTrue(result.contains("Ingegneria del Software"));
        }

        @Test
        @DisplayName("toString con nome null")
        void testToStringConNomeNull() {
            corso.setNome(null);
            String result = corso.toString();

            assertNotNull(result);
            assertTrue(result.contains("Corso"));
        }

        @Test
        @DisplayName("toString con corsoLaurea")
        void testToStringConCorsoLaurea() {
            CorsoLaurea cl = new CorsoLaurea();
            corso.setCorsoLaurea(cl);
            String result = corso.toString();

            assertNotNull(result);
            assertTrue(result.contains("Corso"));
            assertTrue(result.contains("corsoLaurea="));
        }

        @Test
        @DisplayName("toString non è null o vuoto")
        void testToStringNonVuoto() {
            String result = corso.toString();

            assertNotNull(result);
            assertFalse(result.isEmpty());
        }
    }

    @Nested
    @DisplayName("Test di integrazione e scenari complessi")
    class ScenariComplessiTest {

        @Test
        @DisplayName("Creazione completa di un corso con tutte le proprietà")
        void testCreazioneCompleta() {
            Corso corsoCompleto = new Corso("Architettura dei Calcolatori");
            CorsoLaurea cl = new CorsoLaurea();
            AnnoDidattico anno = new AnnoDidattico();

            corsoCompleto.setCorsoLaurea(cl);
            corsoCompleto.setAnnoDidattico(anno);

            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(new Lezione());
            lezioni.add(new Lezione());
            corsoCompleto.setLezioni(lezioni);

            List<Docente> docenti = new ArrayList<>();
            docenti.add(new Docente());
            corsoCompleto.setDocenti(docenti);

            assertEquals("Architettura dei Calcolatori", corsoCompleto.getNome());
            assertEquals(cl, corsoCompleto.getCorsoLaurea());
            assertEquals(anno, corsoCompleto.getAnnoDidattico());
            assertEquals(2, corsoCompleto.getLezioni().size());
            assertEquals(1, corsoCompleto.getDocenti().size());
        }

        @Test
        @DisplayName("Modifica completa di un corso")
        void testModificaCompleta() {
            corso = new Corso("Corso Iniziale");

            corso.setNome("Corso Modificato");
            CorsoLaurea cl = new CorsoLaurea();
            corso.setCorsoLaurea(cl);

            corso.getLezioni().add(new Lezione());
            corso.getDocenti().add(new Docente());

            assertEquals("Corso Modificato", corso.getNome());
            assertEquals(cl, corso.getCorsoLaurea());
            assertEquals(1, corso.getLezioni().size());
            assertEquals(1, corso.getDocenti().size());
        }

        @Test
        @DisplayName("Reset di tutte le proprietà")
        void testResetProprietà() {
            corso = new Corso("Corso Test");
            corso.setCorsoLaurea(new CorsoLaurea());
            corso.setAnnoDidattico(new AnnoDidattico());
            corso.getLezioni().add(new Lezione());
            corso.getDocenti().add(new Docente());

            // Reset
            corso.setNome(null);
            corso.setCorsoLaurea(null);
            corso.setAnnoDidattico(null);
            corso.setLezioni(new ArrayList<>());
            corso.setDocenti(new ArrayList<>());

            assertNull(corso.getNome());
            assertNull(corso.getCorsoLaurea());
            assertNull(corso.getAnnoDidattico());
            assertTrue(corso.getLezioni().isEmpty());
            assertTrue(corso.getDocenti().isEmpty());
        }

        @Test
        @DisplayName("Scambio di proprietà tra due corsi")
        void testScambioProprietà() {
            Corso corso1 = new Corso("Corso 1");
            Corso corso2 = new Corso("Corso 2");

            String tempNome = corso1.getNome();
            CorsoLaurea tempCl = corso1.getCorsoLaurea();

            corso1.setNome(corso2.getNome());
            corso1.setCorsoLaurea(corso2.getCorsoLaurea());

            corso2.setNome(tempNome);
            corso2.setCorsoLaurea(tempCl);

            assertEquals("Corso 2", corso1.getNome());
            assertEquals("Corso 1", corso2.getNome());
        }

        @Test
        @DisplayName("Associazione multiple lezioni e docenti")
        void testAssociazioneMultiple() {
            for (int i = 0; i < 10; i++) {
                corso.getLezioni().add(new Lezione());
                corso.getDocenti().add(new Docente());
            }

            assertEquals(10, corso.getLezioni().size());
            assertEquals(10, corso.getDocenti().size());
        }
    }

    @Nested
    @DisplayName("Test dei valori limite e casi speciali")
    class CasiLimiteTest {

        @Test
        @DisplayName("Nome corso con caratteri speciali")
        void testNomeConCaratteriSpeciali() {
            String nomeSpeciale = "Corso - Lab (A/B) #123";
            corso.setNome(nomeSpeciale);

            assertEquals(nomeSpeciale, corso.getNome());
        }

        @Test
        @DisplayName("Nome corso con Unicode")
        void testNomeConUnicode() {
            String nomeUnicode = "Corso - ñáéíóú";
            corso.setNome(nomeUnicode);

            assertEquals(nomeUnicode, corso.getNome());
        }

        @Test
        @DisplayName("Nome con stringa molto lunga")
        void testNomeConStringaLunga() {
            String nomeLungo = "C".repeat(1000);
            corso.setNome(nomeLungo);

            assertEquals(nomeLungo, corso.getNome());
            assertEquals(1000, corso.getNome().length());
        }

        @Test
        @DisplayName("Lista lezioni con molti elementi")
        void testListaLezioniGrande() {
            for (int i = 0; i < 100; i++) {
                corso.getLezioni().add(new Lezione());
            }

            assertEquals(100, corso.getLezioni().size());
        }

        @Test
        @DisplayName("Lista docenti con molti elementi")
        void testListaDocentiGrande() {
            for (int i = 0; i < 50; i++) {
                corso.getDocenti().add(new Docente());
            }

            assertEquals(50, corso.getDocenti().size());
        }

        @Test
        @DisplayName("Corso senza nome e senza associazioni")
        void testCorsoMinimale() {
            Corso corsoMin = new Corso();

            assertNull(corsoMin.getNome());
            assertNull(corsoMin.getCorsoLaurea());
            assertNull(corsoMin.getAnnoDidattico());
            assertNotNull(corsoMin.getLezioni());
            assertNotNull(corsoMin.getDocenti());
        }
    }

    @Nested
    @DisplayName("Test delle Named Queries (verifica costanti)")
    class NamedQueriesTest {

        @Test
        @DisplayName("Verifica costanti Named Queries sono definite")
        void testCostantiNamedQueries() {
            assertEquals("Corso.trovaCorso", Corso.TROVA_CORSO);
            assertEquals("Corso.trovaTutte", Corso.TROVA_TUTTE);
            assertEquals("Corso.trovaCorsoLaurea", Corso.TROVA_CORSI_CORSOLAUREA);
        }

        @Test
        @DisplayName("Costanti Named Queries non sono null")
        void testCostantiNonNull() {
            assertNotNull(Corso.TROVA_CORSO);
            assertNotNull(Corso.TROVA_TUTTE);
            assertNotNull(Corso.TROVA_CORSI_CORSOLAUREA);
        }

        @Test
        @DisplayName("Costanti Named Queries non sono vuote")
        void testCostantiNonVuote() {
            assertFalse(Corso.TROVA_CORSO.isEmpty());
            assertFalse(Corso.TROVA_TUTTE.isEmpty());
            assertFalse(Corso.TROVA_CORSI_CORSOLAUREA.isEmpty());
        }
    }
}
