package it.unisa.uniclass.testing.unit.orari.service;

import it.unisa.uniclass.orari.model.Giorno;
import it.unisa.uniclass.orari.model.Lezione;
import it.unisa.uniclass.orari.service.LezioneService;
import it.unisa.uniclass.orari.service.dao.LezioneRemote;
import jakarta.persistence.NoResultException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import java.sql.Time;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@DisplayName("Test per la classe LezioneService")
public class LezioneServiceTest {

    @Mock
    private LezioneRemote lezioneDao;

    private LezioneService lezioneService;
    private Lezione lezione;

    @BeforeEach
    void setUp() {
        MockitoAnnotations.openMocks(this);
        lezioneService = new LezioneService(lezioneDao);

        lezione = new Lezione(
                1,
                Time.valueOf("09:00:00"),
                Time.valueOf("11:00:00"),
                Giorno.LUNEDI,
                null,
                null,
                null
        );
    }

    @Nested
    @DisplayName("Test dei costruttori")
    class CostruttoriTest {

        @Test
        @DisplayName("Costruttore con parametro inietta correttamente il DAO")
        void testCostruttoreConParametro() {
            LezioneRemote mockDao = mock(LezioneRemote.class);
            LezioneService service = new LezioneService(mockDao);
            assertNotNull(service);
        }

        @Test
        @DisplayName("Costruttore senza parametri crea comunque l'istanza")
        void testCostruttoreVuoto() {
            LezioneService service = new LezioneService();
            assertNotNull(service);
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaLezione")
    class TrovaLezioneTest {

        @Test
        void testTrovaLezioneSuccesso() {
            when(lezioneDao.trovaLezione(1L)).thenReturn(lezione);
            Lezione result = lezioneService.trovaLezione(1L);
            assertNotNull(result);
            assertEquals(1, result.getSemestre());
        }

        @Test
        void testTrovaLezioneNonTrovata() {
            when(lezioneDao.trovaLezione(999L)).thenThrow(new NoResultException());
            assertNull(lezioneService.trovaLezione(999L));
        }
    }

    @Nested
    @DisplayName("Test trovaLezioniCorso")
    class TrovaLezioniCorsoTest {

        @Test
        void testTrovaLezioniCorsoSuccesso() {
            List<Lezione> lezioni = List.of(lezione);
            when(lezioneDao.trovaLezioniCorso("Programmazione")).thenReturn(lezioni);

            List<Lezione> result = lezioneService.trovaLezioniCorso("Programmazione");

            assertEquals(1, result.size());
        }
    }

    @Nested
    @DisplayName("Test trovaLezioniOre")
    class TrovaLezioniOreTest {

        @Test
        void testTrovaLezioniOreSuccesso() {
            Time inizio = Time.valueOf("09:00:00");
            Time fine = Time.valueOf("11:00:00");

            when(lezioneDao.trovaLezioniOre(inizio, fine)).thenReturn(List.of(lezione));

            List<Lezione> result = lezioneService.trovaLezioniOre(inizio, fine);

            assertEquals(1, result.size());
        }
    }

    @Nested
    @DisplayName("Test trovaLezioniOreGiorno")
    class TrovaLezioniOreGiornoTest {

        @Test
        void testTrovaLezioniOreGiornoSuccesso() {
            Time inizio = Time.valueOf("09:00:00");
            Time fine = Time.valueOf("11:00:00");

            when(lezioneDao.trovaLezioniOreGiorno(inizio, fine, Giorno.LUNEDI))
                    .thenReturn(List.of(lezione));

            List<Lezione> result = lezioneService.trovaLezioniOreGiorno(inizio, fine, Giorno.LUNEDI);

            assertEquals(1, result.size());
        }
    }

    @Nested
    @DisplayName("Test trovaLezioniAule")
    class TrovaLezioniAuleTest {

        @Test
        void testTrovaLezioniAuleSuccesso() {
            when(lezioneDao.trovaLezioniAule("Aula 101")).thenReturn(List.of(lezione));
            assertEquals(1, lezioneService.trovaLezioniAule("Aula 101").size());
        }
    }

    @Nested
    @DisplayName("Test trovaTutte")
    class TrovaTutteTest {

        @Test
        void testTrovaTutteSuccesso() {
            when(lezioneDao.trovaTutte()).thenReturn(List.of(lezione));
            assertEquals(1, lezioneService.trovaTutte().size());
        }
    }

    @Nested
    @DisplayName("Test gestione eccezioni")
    class GestioneEccezioniTest {

        @Test
        void testTrovaTutteEccezione() {
            when(lezioneDao.trovaTutte()).thenThrow(new RuntimeException("DB error"));
            assertThrows(RuntimeException.class, () -> lezioneService.trovaTutte());
        }
    }
}
