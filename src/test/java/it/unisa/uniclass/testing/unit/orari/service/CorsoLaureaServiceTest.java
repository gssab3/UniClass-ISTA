package it.unisa.uniclass.testing.unit.orari.service;

import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.service.CorsoLaureaService;
import it.unisa.uniclass.orari.service.dao.CorsoLaureaRemote;
import jakarta.persistence.NoResultException;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class CorsoLaureaServiceTest {

    @Mock
    private CorsoLaureaRemote corsoLaureaDAO;

    @InjectMocks
    private CorsoLaureaService service;

    // --- TROVA PER ID ---
    @Test
    @DisplayName("Trova per ID: Successo")
    void testTrovaPerId_Success() {
        CorsoLaurea cl = new CorsoLaurea("Informatica");
        when(corsoLaureaDAO.trovaCorsoLaurea(1L)).thenReturn(cl);
        assertEquals(cl, service.trovaCorsoLaurea(1L));
    }

    @Test
    @DisplayName("Trova per ID: Non Trovato (Catch NoResultException)")
    void testTrovaPerId_NotFound() {
        when(corsoLaureaDAO.trovaCorsoLaurea(1L)).thenThrow(new NoResultException());
        assertNull(service.trovaCorsoLaurea(1L));
    }

    // --- TROVA PER NOME ---
    @Test
    @DisplayName("Trova per Nome: Successo")
    void testTrovaPerNome_Success() {
        CorsoLaurea cl = new CorsoLaurea("Informatica");
        when(corsoLaureaDAO.trovaCorsoLaurea("Informatica")).thenReturn(cl);
        assertEquals(cl, service.trovaCorsoLaurea("Informatica"));
    }

    @Test
    @DisplayName("Trova per Nome: Non Trovato")
    void testTrovaPerNome_NotFound() {
        when(corsoLaureaDAO.trovaCorsoLaurea("Ignoto")).thenThrow(new NoResultException());
        assertNull(service.trovaCorsoLaurea("Ignoto"));
    }

    // --- TROVA TUTTI (Exception Wrapping) ---
    @Test
    @DisplayName("Trova Tutti: Successo")
    void testTrovaTutti_Success() {
        when(corsoLaureaDAO.trovaTutti()).thenReturn(Collections.emptyList());
        List<CorsoLaurea> res = service.trovaTutti();
        assertNotNull(res);
    }

    @Test
    @DisplayName("Trova Tutti: Errore DB (Catch Exception -> Throw RuntimeException)")
    void testTrovaTutti_Exception() {
        when(corsoLaureaDAO.trovaTutti()).thenThrow(new RuntimeException("DB Error"));

        RuntimeException thrown = assertThrows(RuntimeException.class, () -> service.trovaTutti());
        assertEquals("Errore durante il recupero dei corsi di laurea.", thrown.getMessage());
    }

    // --- AGGIUNGI (Branch Coverage per Input Validation) ---
    @Test
    @DisplayName("Aggiungi: Successo")
    void testAggiungi_Success() {
        CorsoLaurea cl = new CorsoLaurea("Matematica");
        service.aggiungiCorsoLaurea(cl);
        verify(corsoLaureaDAO).aggiungiCorsoLaurea(cl);
    }

    @Test
    @DisplayName("Aggiungi: Fallimento - Oggetto Null")
    void testAggiungi_NullObject() {
        assertThrows(IllegalArgumentException.class, () -> service.aggiungiCorsoLaurea(null));
        verifyNoInteractions(corsoLaureaDAO);
    }

    @Test
    @DisplayName("Aggiungi: Fallimento - Nome Null")
    void testAggiungi_NullName() {
        CorsoLaurea cl = new CorsoLaurea(null);
        assertThrows(IllegalArgumentException.class, () -> service.aggiungiCorsoLaurea(cl));
    }

    @Test
    @DisplayName("Aggiungi: Fallimento - Nome Vuoto")
    void testAggiungi_EmptyName() {
        CorsoLaurea cl = new CorsoLaurea("");
        assertThrows(IllegalArgumentException.class, () -> service.aggiungiCorsoLaurea(cl));
    }

    // --- RIMUOVI ---
    @Test
    @DisplayName("Rimuovi: Successo")
    void testRimuovi_Success() {
        CorsoLaurea cl = new CorsoLaurea();
        service.rimuoviCorsoLaurea(cl);
        verify(corsoLaureaDAO).rimuoviCorsoLaurea(cl);
    }

    @Test
    @DisplayName("Rimuovi: Fallimento - Null")
    void testRimuovi_Null() {
        assertThrows(IllegalArgumentException.class, () -> service.rimuoviCorsoLaurea(null));
        verifyNoInteractions(corsoLaureaDAO);
    }
}