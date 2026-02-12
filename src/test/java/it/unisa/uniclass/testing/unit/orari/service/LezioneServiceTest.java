package it.unisa.uniclass.testing.unit.orari.service;

import it.unisa.uniclass.orari.model.Giorno;
import it.unisa.uniclass.orari.model.Lezione;
import it.unisa.uniclass.orari.service.LezioneService;
import it.unisa.uniclass.orari.service.dao.LezioneRemote;
import jakarta.persistence.NoResultException;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.Time;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class LezioneServiceTest {

    @Mock
    private LezioneRemote lezioneDao;

    @InjectMocks
    private LezioneService service;

    @Test
    @DisplayName("Trova Lezione: Successo e Catch NoResultException")
    void testTrovaLezione() {
        Lezione l = new Lezione();
        when(lezioneDao.trovaLezione(1L)).thenReturn(l);
        assertSame(l, service.trovaLezione(1L));

        when(lezioneDao.trovaLezione(99L)).thenThrow(new NoResultException());
        assertNull(service.trovaLezione(99L));
    }

    @Test
    @DisplayName("Test deleghe metodi di ricerca")
    void testRicerche() {
        Time t1 = Time.valueOf("09:00:00");
        Time t2 = Time.valueOf("11:00:00");

        service.trovaLezioniCorso("Corso");
        service.trovaLezioniOre(t1, t2);
        service.trovaLezioniOreGiorno(t1, t2, Giorno.LUNEDI);
        service.trovaLezioniAule("F1");
        service.trovaTutte();
        service.trovaLezioniCorsoLaureaRestoAnno(1, 2, 3);
        service.trovaLezioniCorsoLaureaRestoAnnoSemestre(1, 2, 3, 1);
        service.trovaLezioniDocente("Rossi");

        verify(lezioneDao).trovaLezioniDocente("Rossi");
        verify(lezioneDao).trovaLezioniAule("F1");
    }

    @Test
    @DisplayName("Test deleghe aggiungi e rimuovi")
    void testSalvataggio() {
        Lezione l = new Lezione();
        service.aggiungiLezione(l);
        verify(lezioneDao).aggiungiLezione(l);

        service.rimuoviLezione(l);
        verify(lezioneDao).rimuoviLezione(l);
    }
}